{-# LANGUAGE NoMonomorphismRestriction #-}

module CrossCodegen where

{-
A special cross-compilation mode for hsc2hs, which generates a .hs
file without needing to run the executables that the C compiler
outputs.

Instead, it uses the output of compilations only -- specifically,
whether compilation fails.  This is the same trick that autoconf uses
when cross compiling; if you want to know if sizeof(int) <= 4, then try
compiling:

> int x() {
>   static int ary[1 - 2*(sizeof(int) <= 4)];
> }

and see if it fails. If you want to know sizeof(int), then
repeatedly apply this kind of test with differing values, using
binary search.
-}

import Prelude hiding (concatMap)
import System.IO (hPutStr, openFile, IOMode(..), hClose)
import System.Directory (removeFile)
import Data.Char (toLower,toUpper,isSpace)
import Control.Exception (assert, evaluate, onException, try, SomeException)
import Control.Monad (when, liftM, forM, ap)
import Control.Applicative as AP (Applicative(..))
import Data.Foldable (concatMap)
import Data.Maybe (fromMaybe)
import qualified Data.Sequence as S
import Data.Sequence ((|>),ViewL(..))
import System.Exit ( ExitCode(..) )
import System.Process

import C
import Common
import Flags
import HSCParser

import qualified ATTParser as ATT
import qualified Data.Map.Strict as Map

-- A monad over IO for performing tests; keeps the command line flags
-- and a state counter for unique filename generation.
-- equivalent to ErrorT String (StateT Int (ReaderT TestMonadEnv IO))
newtype TestMonad a = TestMonad { runTest :: TestMonadEnv -> Int -> IO (Either String a, Int) }

instance Functor TestMonad where
    fmap = liftM

instance Applicative TestMonad where
    pure a = TestMonad (\_ c -> pure (Right a, c))
    (<*>) = ap

instance Monad TestMonad where
    return = AP.pure
    x >>= fn = TestMonad (\e c -> (runTest x e c) >>=
                                      (\(a,c') -> either (\err -> return (Left err, c'))
                                                         (\result -> runTest (fn result) e c')
                                                         a))

data TestMonadEnv = TestMonadEnv {
    testIsVerbose_ :: Bool,
    testLogNestCount_ :: Int,
    testKeepFiles_ :: Bool,
    testGetBaseName_ :: FilePath,
    testGetFlags_ :: [Flag],
    testGetConfig_ :: Config,
    testGetCompiler_ :: FilePath
}

testAsk :: TestMonad TestMonadEnv
testAsk = TestMonad (\e c -> return (Right e, c))

testIsVerbose :: TestMonad Bool
testIsVerbose = testIsVerbose_ `fmap` testAsk

testGetCompiler :: TestMonad FilePath
testGetCompiler = testGetCompiler_ `fmap` testAsk

testKeepFiles :: TestMonad Bool
testKeepFiles = testKeepFiles_ `fmap` testAsk

testGetFlags :: TestMonad [Flag]
testGetFlags = testGetFlags_ `fmap` testAsk

testGetConfig :: TestMonad Config
testGetConfig = testGetConfig_ `fmap` testAsk

testGetBaseName :: TestMonad FilePath
testGetBaseName = testGetBaseName_ `fmap` testAsk

testIncCount :: TestMonad Int
testIncCount = TestMonad (\_ c -> let next=succ c
                                  in next `seq` return (Right c, next))
testFail' :: String -> TestMonad a
testFail' s = TestMonad (\_ c -> return (Left s, c))

testFail :: SourcePos -> String -> TestMonad a
testFail (SourcePos file line _) s = testFail' (file ++ ":" ++ show line ++ " " ++ s)

-- liftIO for TestMonad
liftTestIO :: IO a -> TestMonad a
liftTestIO x = TestMonad (\_ c -> x >>= \r -> return (Right r, c))

-- finally for TestMonad
testFinally :: TestMonad a -> TestMonad b -> TestMonad a
testFinally action cleanup = do r <- action `testOnException` cleanup
                                _ <- cleanup
                                return r

-- onException for TestMonad. This rolls back the state on an
-- IO exception, which isn't great but shouldn't matter for now
-- since only the test count is stored there.
testOnException :: TestMonad a -> TestMonad b -> TestMonad a
testOnException action cleanup = TestMonad (\e c -> runTest action e c
                                                        `onException` runTest cleanup e c >>= \(actionResult,c') ->
                                                        case actionResult of
                                                           Left _ -> do (_,c'') <- runTest cleanup e c'
                                                                        return (actionResult,c'')
                                                           Right _ -> return (actionResult,c'))

-- prints the string to stdout if verbose mode is enabled.
-- Maintains a nesting count and pads with spaces so that:
-- testLog "a" $
--    testLog "b" $ return ()
-- will print
-- a
--     b
testLog :: String -> TestMonad a -> TestMonad a
testLog s a = TestMonad (\e c -> do let verbose = testIsVerbose_ e
                                        nestCount = testLogNestCount_ e
                                    when verbose $ putStrLn $ (concat $ replicate nestCount "    ") ++ s
                                    runTest a (e { testLogNestCount_ = nestCount+1 }) c)

testLog' :: String -> TestMonad ()
testLog' s = testLog s (return ())

testLogAtPos :: SourcePos -> String -> TestMonad a -> TestMonad a
testLogAtPos (SourcePos file line _) s a = testLog (file ++ ":" ++ show line ++ " " ++ s) a

-- Given a list of file suffixes, will generate a list of filenames
-- which are all unique and have the given suffixes. On exit from this
-- action, all those files will be removed (unless keepFiles is active)
makeTest :: [String] -> ([String] -> TestMonad a) -> TestMonad a
makeTest fileSuffixes fn = do
    c <- testIncCount
    fileBase <- testGetBaseName
    keepFiles <- testKeepFiles
    let files = zipWith (++) (repeat (fileBase ++ show c)) fileSuffixes
    testFinally (fn files)
                (when (not keepFiles)
                      (mapM_ removeOrIgnore files))
    where
     removeOrIgnore f = liftTestIO (catchIO (removeFile f) (const $ return ()))
-- Convert from lists to tuples (to avoid "incomplete pattern" warnings in the callers)
makeTest2 :: (String,String) -> ((String,String) -> TestMonad a) -> TestMonad a
makeTest2 (a,b) fn = makeTest [a,b] helper
    where helper [a',b'] = fn (a',b')
          helper _ = error "makeTest: internal error"
makeTest3 :: (String,String,String) -> ((String,String,String) -> TestMonad a) -> TestMonad a
makeTest3 (a,b,c) fn = makeTest [a,b,c] helper
    where helper [a',b',c'] = fn (a',b',c')
          helper _ = error "makeTest: internal error"

-- A Zipper over lists. Unlike ListZipper, this separates at the type level
-- a list which may have a currently focused item (Zipper a) from
-- a list which _definitely_ has a focused item (ZCursor a), so
-- that zNext can be total.
data Zipper a = End { zEnd :: S.Seq a }
              | Zipper (ZCursor a)

data ZCursor a = ZCursor { zCursor :: a,
                           zAbove :: S.Seq a, -- elements prior to the cursor
                                              -- in regular order (not reversed!)
                           zBelow :: S.Seq a -- elements after the cursor
                         }

zipFromList :: [a] -> Zipper a
zipFromList [] = End S.empty
zipFromList (l:ls) = Zipper (ZCursor l S.empty (S.fromList ls))

zNext :: ZCursor a -> Zipper a
zNext (ZCursor c above below) =
    case S.viewl below of
      S.EmptyL -> End (above |> c)
      c' :< below' -> Zipper (ZCursor c' (above |> c) below')

------------------------------------------------------------------------
-- Batch compilation: reduces hundreds of individual C compilations
-- to a single compilation by collecting all constant-like directives,
-- compiling them in one go to assembly, and extracting all results.
------------------------------------------------------------------------

-- | Unique identifier for each batched constant.
type BatchId = Int

-- | A conditional frame captures all the preprocessor directives needed
-- to establish the conditional context for one nesting level.
-- E.g. for "#ifdef A" followed by "#else", the frame is
-- ["#ifdef A\n", "#else\n"].
type CondFrame = [String]

-- | Stack of conditional frames, innermost first (most recent on top).
type CondStack = [CondFrame]

-- | A single batch entry: a C expression to evaluate with its
-- conditional context.
data BatchEntry = BatchEntry
    { beId   :: !BatchId
    , beExpr :: !String
    , beCond :: !CondStack
    }

-- | Index for looking up batch IDs by source position.
data BatchIndex = BatchIndex
    { biSimple :: !(Map.Map (Int, Int) BatchId)
      -- ^ (line, col) -> batch ID for const/size/alignment/offset/peek/poke/ptr
    , biEnum   :: !(Map.Map (Int, Int) [(Maybe String, String, BatchId)])
      -- ^ (line, col) -> [(hsName, cName, batchId)] for enum directives
    }

-- | Pre-resolved batch results for fast lookup during output.
data ResolvedBatch = ResolvedBatch
    { rbConsts :: !(Map.Map (Int, Int) Integer)
      -- ^ (line, col) -> value for simple directives
    , rbEnums  :: !(Map.Map (Int, Int) [(Maybe String, String, Integer)])
      -- ^ (line, col) -> [(hsName, cName, value)] for enum directives
    }

-- | Empty batch results (no pre-computed values).
emptyBatch :: ResolvedBatch
emptyBatch = ResolvedBatch Map.empty Map.empty

-- | Walk the token stream and collect all batchable directives with
-- their conditional context. Returns the list of batch entries and
-- an index for looking up results by source position.
collectBatchEntries :: [Token] -> ([BatchEntry], BatchIndex)
collectBatchEntries toks = go 0 [] [] Map.empty Map.empty toks
  where
    go _nextId _cond entries simpleIdx enumIdx [] =
        (reverse entries, BatchIndex simpleIdx enumIdx)
    go nextId cond entries simpleIdx enumIdx (tok : rest) = case tok of
        Special pos key value
            -- Push a new conditional frame
            | key `elem` ["if", "ifdef", "ifndef"] ->
                let frame = ["#" ++ key ++ " " ++ value ++ "\n"]
                in go nextId (frame : cond) entries simpleIdx enumIdx rest
            -- Extend the current innermost frame with elif
            | key == "elif" -> case cond of
                (frame : frames) ->
                    go nextId ((frame ++ ["#elif " ++ value ++ "\n"]) : frames)
                       entries simpleIdx enumIdx rest
                [] -> go nextId cond entries simpleIdx enumIdx rest
            -- Extend the current innermost frame with else
            | key == "else" -> case cond of
                (frame : frames) ->
                    go nextId ((frame ++ ["#else\n"]) : frames)
                       entries simpleIdx enumIdx rest
                [] -> go nextId cond entries simpleIdx enumIdx rest
            -- Pop the innermost frame
            | key == "endif" -> case cond of
                (_ : frames) -> go nextId frames entries simpleIdx enumIdx rest
                []           -> go nextId [] entries simpleIdx enumIdx rest
            -- Batchable simple directives
            | key == "const" ->
                addSimple nextId cond pos value entries simpleIdx enumIdx rest
            | key == "size" ->
                addSimple nextId cond pos ("sizeof(" ++ value ++ ")")
                    entries simpleIdx enumIdx rest
            | key == "alignment" ->
                addSimple nextId cond pos (alignment value)
                    entries simpleIdx enumIdx rest
            | key `elem` ["offset", "peek", "poke", "ptr"] ->
                addSimple nextId cond pos ("offsetof(" ++ value ++ ")")
                    entries simpleIdx enumIdx rest
            -- Enum: multiple constants per directive
            | key == "enum" -> case parseEnum value of
                Nothing -> go nextId cond entries simpleIdx enumIdx rest
                Just (_, _, enums) ->
                    let (nextId', newEntries, lookupEntries) =
                            mkEnumEntries nextId cond enums
                        SourcePos _ l c = pos
                        enumIdx' = Map.insert (l, c) lookupEntries enumIdx
                    in go nextId' cond (reverse newEntries ++ entries)
                          simpleIdx enumIdx' rest
            -- Non-batchable directives (type, include, define, etc.)
            | otherwise -> go nextId cond entries simpleIdx enumIdx rest
        -- Text tokens: skip
        _ -> go nextId cond entries simpleIdx enumIdx rest

    addSimple nextId cond pos cExpr entries simpleIdx enumIdx rest =
        let entry = BatchEntry nextId cExpr cond
            SourcePos _ l c = pos
            simpleIdx' = Map.insert (l, c) nextId simpleIdx
        in go (nextId + 1) cond (entry : entries) simpleIdx' enumIdx rest

    mkEnumEntries nextId _ [] = (nextId, [], [])
    mkEnumEntries nextId cond ((hsName, cName) : more) =
        let entry = BatchEntry nextId cName cond
            (nextId', moreEntries, moreLookup) =
                mkEnumEntries (nextId + 1) cond more
        in (nextId', entry : moreEntries, (hsName, cName, nextId) : moreLookup)

-- | Generate a single C source file that computes all batch entries.
-- The file includes the full header context (template, flags, all
-- preprocessor directives from the .hsc file) followed by the batch
-- entries, each wrapped in their conditional guards.
generateBatchC :: Config -> [Flag] -> [Token] -> [BatchEntry] -> String
generateBatchC config flags toks entries =
    -- Preamble: reproduces the file's include/define/conditional context
    outTemplateHeaderCProg (cTemplate config) ++
    concatMap outFlagHeaderCProg flags ++
    concatMap outHeaderCProg' toks ++
    -- BOM marker for endianness detection (used by ATTParser)
    "\nextern unsigned long long ___hsc2hs_BOM___;\n" ++
    "unsigned long long ___hsc2hs_BOM___ = 0x100000000;\n\n" ++
    -- All batch entries with their conditional guards
    concatMap emitEntry entries
  where
    emitEntry (BatchEntry bid cExpr cond) =
        let name      = "_hsc2hs_v" ++ show bid
            -- Reverse cond stack to get outermost-first order for C output
            outerFirst = reverse cond
            openCond   = concatMap concat outerFirst
            closeCond  = concat (replicate (length cond) "#endif\n")
        in  openCond ++
            "extern unsigned long long " ++ name ++ "___hsc2hs_sign___;\n" ++
            "unsigned long long " ++ name ++ "___hsc2hs_sign___ = (" ++
                cExpr ++ ") < 0;\n" ++
            "extern unsigned long long " ++ name ++ ";\n" ++
            "unsigned long long " ++ name ++ " = (" ++ cExpr ++ ");\n" ++
            closeCond ++ "\n"

-- | Compile all batch entries in a single C -> assembly compilation,
-- then parse the assembly to extract all constant values.
-- Returns a map from batch ID to extracted integer value.
-- On failure, returns an empty map (callers fall through to the
-- per-directive path).
runBatchCompile :: [BatchEntry] -> [Token] -> TestMonad (Map.Map BatchId Integer)
runBatchCompile entries toks = do
    config <- testGetConfig
    flags <- testGetFlags
    let cSource = generateBatchC config flags toks entries
    testLog ("batch compiling " ++ show (length entries) ++ " constants") $ do
        result <- makeTest3 (".c", ".s", ".txt") $ \(cFile, sFile, stdout) -> do
            liftTestIO $ writeBinaryFile cFile cSource
            compiler <- testGetCompiler
            -- -g0 suppresses debug/DWARF sections that produce assembly
            -- directives (e.g. .quad/.long sequences in .debug_info) which
            -- the ATT parser cannot handle. We only need constant values.
            success <- runCompiler compiler
                           (["-S", "-c", "-g0", cFile, "-o", sFile] ++
                            [f | CompFlag f <- flags])
                           (Just stdout)
            if success
                then do
                    -- Use try to catch parse errors gracefully. This handles
                    -- compilers that produce non-AT&T assembly (e.g. emcc
                    -- producing WebAssembly text). On failure, we return an
                    -- empty map so each directive falls through to the
                    -- existing per-directive compilation path.
                    --
                    -- We must force the spine of the parse result inside the
                    -- try block: ATT.parse returns a lazy thunk, so without
                    -- forcing, errors escape the try scope entirely.
                    parseResult <- liftTestIO $
                        (try (do asm <- ATT.parse sFile
                                 _ <- evaluate (length asm)
                                 return asm)
                            :: IO (Either SomeException [(String, ATT.Inst)]))
                    case parseResult of
                        Right asm -> return $ Map.fromList
                            [ (beId entry, val)
                            | entry <- entries
                            , let name = "_hsc2hs_v" ++ show (beId entry)
                            , Just val <- [ATT.lookupInteger name asm]
                            ]
                        Left _e -> return Map.empty
                else return Map.empty
        testLog' $ "batch resolved " ++ show (Map.size result) ++
                   " of " ++ show (length entries) ++ " constants"
        return result

-- | Resolve batch compilation results into fast-lookup maps keyed by
-- source position (line, col).
resolveBatch :: Map.Map BatchId Integer -> BatchIndex -> ResolvedBatch
resolveBatch results idx = ResolvedBatch
    { rbConsts = Map.mapMaybe (\bid -> Map.lookup bid results) (biSimple idx)
    , rbEnums  = Map.mapMaybe resolveEnum (biEnum idx)
    }
  where
    resolveEnum enumEntries =
        let resolved = [ (hs, c, val)
                       | (hs, c, bid) <- enumEntries
                       , Just val <- [Map.lookup bid results]
                       ]
        -- Only return resolved list if ALL enum values were found;
        -- partial resolution falls through to per-directive path.
        in if length resolved == length enumEntries
           then Just resolved
           else Nothing

-- Generates the .hs file from the .hsc file, by looping over each
-- Special element and calling outputSpecial to find out what it needs.
diagnose :: ResolvedBatch -> String -> (String -> TestMonad ()) -> [Token] -> TestMonad ()
diagnose batch inputFilename output input = do
    checkValidity input
    output ("{-# LINE 1 \"" ++ inputFilename ++ "\" #-}\n")
    loop (True, True) (zipFromList input)

    where
    loop _ (End _) = return ()
    loop state@(lineSync, colSync)
         (Zipper z@ZCursor {zCursor=Special _ key _}) =
        case key of
            _ | key `elem` ["if","ifdef","ifndef","elif","else"] -> do
                condHolds <- checkConditional z
                if condHolds
                    then loop state (zNext z)
                    else loop state =<< either testFail' return
                                               (skipFalseConditional (zNext z))
            "endif" -> loop state (zNext z)
            _ -> do
                sync <- outputSpecial batch output z
                loop (lineSync && sync, colSync && sync) (zNext z)
    loop state (Zipper z@ZCursor {zCursor=Text pos txt}) = do
        state' <- outputText state output pos txt
        loop state' (zNext z)

outputSpecial :: ResolvedBatch -> (String -> TestMonad ()) -> ZCursor Token -> TestMonad Bool
outputSpecial batch output (z@ZCursor {zCursor=Special pos@(SourcePos file line col) key value}) =
    case key of
       "const" -> outputConst value show >> return False
       "offset" -> outputConst ("offsetof(" ++ value ++ ")") (\i -> "(" ++ show i ++ ")") >> return False
       "size" -> outputConst ("sizeof(" ++ value ++ ")") (\i -> "(" ++ show i ++ ")") >> return False
       "alignment" -> outputConst (alignment value) show >> return False
       "peek" -> outputConst ("offsetof(" ++ value ++ ")")
                             (\i -> "(\\hsc_ptr -> peekByteOff hsc_ptr " ++ show i ++ ")") >> return False
       "poke" -> outputConst ("offsetof(" ++ value ++ ")")
                             (\i -> "(\\hsc_ptr -> pokeByteOff hsc_ptr " ++ show i ++ ")") >> return False
       "ptr" -> outputConst ("offsetof(" ++ value ++ ")")
                            (\i -> "(\\hsc_ptr -> hsc_ptr `plusPtr` " ++ show i ++ ")") >> return False
       "type" -> computeType z >>= output >> return False
       "enum" -> computeEnumBatch batch z >>= output >> return False
       "error" -> testFail pos ("#error " ++ value)
       "warning" -> liftTestIO $ putStrLn (file ++ ":" ++ show line ++ " warning: " ++ value) >> return True
       "include" -> return True
       "define" -> return True
       "undef" -> return True
       _ -> testFail pos ("directive " ++ key ++ " cannot be handled in cross-compilation mode")
    where
    posKey = (line, col)
    -- Fast path: look up pre-computed value from batch results.
    -- Falls through to per-directive computeConst on miss.
    outputConst cExpr formatter =
        case Map.lookup posKey (rbConsts batch) of
            Just val -> output (formatter val)
            Nothing  -> computeConst z cExpr >>= (output . formatter)
outputSpecial _ _ _ = error "outputSpecial's argument isn't a Special"

outputText :: (Bool, Bool) -> (String -> TestMonad ()) -> SourcePos -> String
           -> TestMonad (Bool, Bool)
outputText state output pos txt = do
    enableCol <- fmap cColumn testGetConfig
    let outCol col | enableCol = "{-# COLUMN " ++ show col ++ " #-}"
                   | otherwise = ""
    let outLine (SourcePos file line _) = "{-# LINE " ++ show (line + 1) ++
                                          " \"" ++ file ++ "\" #-}\n"
    let (s, state') = outTextHs state pos txt id outLine outCol
    output s
    return state'

-- Bleh, messy. For each test we're compiling, we have a specific line of
-- code that may cause compiler errors -- that's the test we want to perform.
-- However, we *really* don't want any other kinds of compiler errors sneaking
-- in (which might be e.g. due to the user's syntax errors) or we'll make the
-- wrong conclusions on our tests.
--
-- So before we compile any of the tests, take a pass over the whole file and
-- generate a .c file which should fail if there are any syntax errors in what
-- the user gave us. Hopefully, then the only reason our later compilations
-- might fail is the particular reason we want.
--
-- Another approach would be to try to parse the stdout of GCC and diagnose
-- whether the error is the one we want. That's tricky because of localization
-- etc. etc., though it would be less nerve-wracking. FYI it's not the approach
-- that autoconf went with.
checkValidity :: [Token] -> TestMonad ()
checkValidity input = do
    config <- testGetConfig
    flags <- testGetFlags
    let test = outTemplateHeaderCProg (cTemplate config) ++
               concatMap outFlagHeaderCProg flags ++
               concatMap (uncurry (outValidityCheck (cViaAsm config))) (zip input [0..])
    testLog ("checking for compilation errors") $ do
        success <- makeTest2 (".c",".o") $ \(cFile,oFile) -> do
            liftTestIO $ writeBinaryFile cFile test
            compiler <- testGetCompiler
            runCompiler compiler
                        (["-S" | cViaAsm config ]++
                         ["-c",cFile,"-o",oFile]++
                         [f | CompFlag f <- flags])
                        Nothing
        when (not success) $ testFail' "compilation failed"
    testLog' "compilation is error-free"

outValidityCheck :: Bool -> Token -> Int -> String
outValidityCheck viaAsm s@(Special pos key value) uniq =
    case key of
       "const" -> checkValidConst value
       "offset" -> checkValidConst ("offsetof(" ++ value ++ ")")
       "size" -> checkValidConst ("sizeof(" ++ value ++ ")")
       "alignment" -> checkValidConst (alignment value)
       "peek" -> checkValidConst ("offsetof(" ++ value ++ ")")
       "poke" -> checkValidConst ("offsetof(" ++ value ++ ")")
       "ptr" -> checkValidConst ("offsetof(" ++ value ++ ")")
       "type" -> checkValidType
       "enum" -> checkValidEnum
       _ -> outHeaderCProg' s
    where
    checkValidConst value' = if viaAsm
                             then validConstTestViaAsm (show uniq) value' ++ "\n"
                             else "void _hsc2hs_test" ++ show uniq ++ "()\n{\n" ++ validConstTest value' ++ "}\n"
    checkValidType = "void _hsc2hs_test" ++ show uniq ++ "()\n{\n" ++ outCLine pos ++ "    (void)(" ++ value ++ ")1;\n}\n";
    checkValidEnum =
        case parseEnum value of
            Nothing -> ""
            Just (_,_,enums) | viaAsm ->
                concatMap (\(hName,cName) -> validConstTestViaAsm (fromMaybe "noKey" (ATT.trim `fmap` hName) ++ show uniq) cName) enums
            Just (_,_,enums) ->
                "void _hsc2hs_test" ++ show uniq ++ "()\n{\n" ++
                concatMap (\(_,cName) -> validConstTest cName) enums ++
                "}\n"

    -- we want this to fail if the value is syntactically invalid or isn't a constant
    validConstTest value' = outCLine pos ++ "    {\n        static int test_array[(" ++ value' ++ ") > 0 ? 2 : 1];\n        (void)test_array;\n    }\n"
    validConstTestViaAsm name value' = outCLine pos ++ "\nextern long long _hsc2hs_test_" ++ name ++";\n"
                                                    ++ "long long _hsc2hs_test_" ++ name ++ " = (" ++ value' ++ ");\n"

outValidityCheck _ (Text _ _) _ = ""

-- Skips over some #if or other conditional that we found to be false.
-- I.e. the argument should be a zipper whose cursor is one past the #if,
-- and returns a zipper whose cursor points at the next item which
-- could possibly be compiled.
skipFalseConditional :: Zipper Token -> Either String (Zipper Token)
skipFalseConditional (End _) = Left "unterminated endif"
skipFalseConditional (Zipper z@(ZCursor {zCursor=Special _ key _})) =
    case key of
      "if" -> either Left skipFalseConditional $ skipFullConditional 0 (zNext z)
      "ifdef" -> either Left skipFalseConditional $ skipFullConditional 0 (zNext z)
      "ifndef" -> either Left skipFalseConditional $ skipFullConditional 0 (zNext z)
      "elif" -> Right $ Zipper z
      "else" -> Right $ Zipper z
      "endif" -> Right $ zNext z
      _ -> skipFalseConditional (zNext z)
skipFalseConditional (Zipper z) = skipFalseConditional (zNext z)

-- Skips over an #if all the way to the #endif
skipFullConditional :: Int -> Zipper Token -> Either String (Zipper Token)
skipFullConditional _ (End _) = Left "unterminated endif"
skipFullConditional nest (Zipper z@(ZCursor {zCursor=Special _ key _})) =
    case key of
      "if" -> skipFullConditional (nest+1) (zNext z)
      "ifdef" -> skipFullConditional (nest+1) (zNext z)
      "ifndef" -> skipFullConditional (nest+1) (zNext z)
      "endif" | nest > 0 -> skipFullConditional (nest-1) (zNext z)
      "endif" | otherwise -> Right $ zNext z
      _ -> skipFullConditional nest (zNext z)
skipFullConditional nest (Zipper z) = skipFullConditional nest (zNext z)

data IntegerConstant = Signed Integer |
                       Unsigned Integer deriving (Show)
-- Prints an syntatically valid integer in C
cShowInteger :: IntegerConstant -> String
cShowInteger (Signed x) | x < 0 = "(" ++ show (x+1) ++ "-1)"
                                  -- Trick to avoid overflowing large integer constants
                                  -- http://www.hardtoc.com/archives/119
cShowInteger (Signed x) = show x
cShowInteger (Unsigned x) = show x ++ "u"

data IntegerComparison = GreaterOrEqual IntegerConstant |
                         LessOrEqual IntegerConstant
instance Show IntegerComparison where
    showsPrec _ (GreaterOrEqual c) = showString "`GreaterOrEqual` " . shows c
    showsPrec _ (LessOrEqual c) = showString "`LessOrEqual` " . shows c

cShowCmpTest :: IntegerComparison -> String
cShowCmpTest (GreaterOrEqual x) = ">=" ++ cShowInteger x
cShowCmpTest (LessOrEqual x) = "<=" ++ cShowInteger x

-- The cursor should point at #{const SOME_VALUE} or something like that.
-- Determines the value of SOME_VALUE using binary search; this
-- is a trick which is cribbed from autoconf's AC_COMPUTE_INT.
computeConst :: ZCursor Token -> String -> TestMonad Integer
computeConst zOrig@(ZCursor (Special pos _ _) _ _) value =
    testLogAtPos pos ("computing " ++ value) $ do
        config <- testGetConfig
        int <- case cViaAsm config of
                 True -> runCompileAsmIntegerTest z
                 False -> do nonNegative <- compareConst z (GreaterOrEqual (Signed 0))
                             integral <- checkValueIsIntegral z nonNegative
                             when (not integral) $ testFail pos $ value ++ " is not an integer"
                             (lower,upper) <- bracketBounds z nonNegative
                             binarySearch z nonNegative lower upper
        testLog' $ "result: " ++ show int
        return int
    where -- replace the Special's value with the provided value; e.g. the special
          -- is #{size SOMETHING} and we might replace value with "sizeof(SOMETHING)".
          z = zOrig {zCursor=specialSetValue value (zCursor zOrig)}
          specialSetValue v (Special p k _) = Special p k v
          specialSetValue _ _ = error "computeConst argument isn't a Special"
computeConst _ _ = error "computeConst argument isn't a Special"

-- Binary search, once we've bracketed the integer.
binarySearch :: ZCursor Token -> Bool -> Integer -> Integer -> TestMonad Integer
binarySearch _ _ l u | l == u = return l
binarySearch z nonNegative l u = do
    let mid :: Integer
        mid = (l+u+1) `div` 2
    inTopHalf <- compareConst z (GreaterOrEqual $ (if nonNegative then Unsigned else Signed) mid)
    let (l',u') = if inTopHalf then (mid,u) else (l,(mid-1))
    assert (l < mid && mid <= u &&             -- @l < mid <= u@
            l <= l' && l' <= u' && u' <= u &&  -- @l <= l' <= u' <= u@
            u'-l' < u-l)                       -- @|u' - l'| < |u - l|@
           (binarySearch z nonNegative l' u')

-- Establishes bounds on the unknown integer. By searching increasingly
-- large powers of 2, it'll bracket an integer x by lower & upper
-- such that lower <= x <= upper.
--
-- Assumes 2's complement integers.
bracketBounds :: ZCursor Token -> Bool -> TestMonad (Integer, Integer)
bracketBounds z nonNegative = do
    let -- test against integers 2**x-1 when positive, and 2**x when negative,
        -- to avoid generating constants that'd overflow the machine's integers.
        -- I.e. suppose we're searching for #{const INT_MAX} (e.g. 2^32-1).
        -- If we're comparing against all 2**x-1, we'll stop our search
        -- before we ever overflow int.
        powersOfTwo = iterate (\a -> 2*a) 1
        positiveBounds = map pred powersOfTwo
        negativeBounds = map negate powersOfTwo

        -- Test each element of the bounds list until we find one that exceeds
        -- the integer.
        loop cmp inner (maybeOuter:bounds') = do
          outerBounded <- compareConst z (cmp maybeOuter)
          if outerBounded
            then return (inner,maybeOuter)
            else loop cmp maybeOuter bounds'
        loop _ _ _ = error "bracketBounds: infinite list exhausted"

    if nonNegative
      then do (inner,outer) <- loop (LessOrEqual . Unsigned) (-1) positiveBounds
              return (inner+1,outer)
      else do (inner,outer) <- loop (GreaterOrEqual . Signed) 0 negativeBounds
              return (outer,inner-1)

-- For #{enum} codegen; mimics template-hsc.h's hsc_haskellize
haskellize :: String -> String
haskellize [] = []
haskellize (firstLetter:next) = toLower firstLetter : loop False next
    where loop _ [] = []
          loop _ ('_':as) = loop True as
          loop upper (a:as) = (if upper then toUpper a else toLower a) : loop False as

-- For #{enum} codegen; in normal hsc2hs, any whitespace in the enum types &
-- constructors will be mangled by the C preprocessor. This mimics the same
-- mangling.
stringify :: String -> String
-- Spec: stringify = unwords . words
stringify = go False . dropWhile isSpace
  where
    go _haveSpace [] = []
    go  haveSpace (x:xs)
      | isSpace x = go True xs
      | otherwise = if haveSpace
                    then ' ' : x : go False xs
                    else x : go False xs

-- For #{alignment} codegen; mimic's template-hsc.h's hsc_alignment
alignment :: String -> String
alignment t = "offsetof(struct {char x__; " ++ t ++ " (y__); }, y__)"

computeEnum :: ZCursor Token -> TestMonad String
computeEnum z@(ZCursor (Special _ _ enumText) _ _) =
    case parseEnum enumText of
        Nothing -> return ""
        Just (enumType,constructor,enums) ->
            concatM enums $ \(maybeHsName, cName) -> do
                constValue <- computeConst z cName
                let hsName = fromMaybe (haskellize cName) maybeHsName
                return $
                    hsName ++ " :: " ++ stringify enumType ++ "\n" ++
                    hsName ++ " = " ++ stringify constructor ++ " " ++ showsPrec 11 constValue "\n"
    where concatM l = liftM concat . forM l
computeEnum _ = error "computeEnum argument isn't a Special"

-- | Batch-aware enum computation. Checks the batch results first;
-- falls through to per-directive computeEnum on miss.
computeEnumBatch :: ResolvedBatch -> ZCursor Token -> TestMonad String
computeEnumBatch batch z@(ZCursor (Special (SourcePos _ line col) _ enumText) _ _) =
    case Map.lookup (line, col) (rbEnums batch) of
        Just resolvedEnums ->
            case parseEnum enumText of
                Nothing -> return ""
                Just (enumType, constructor, _) ->
                    return $ concat
                        [ hsName ++ " :: " ++ stringify enumType ++ "\n" ++
                          hsName ++ " = " ++ stringify constructor ++ " " ++
                          showsPrec 11 val "\n"
                        | (maybeHsName, cName, val) <- resolvedEnums
                        , let hsName = fromMaybe (haskellize cName) maybeHsName
                        ]
        Nothing -> computeEnum z
computeEnumBatch _ _ = error "computeEnumBatch argument isn't a Special"

-- Implementation of #{type}, using computeConst
computeType :: ZCursor Token -> TestMonad String
computeType z@(ZCursor (Special pos _ value) _ _) = do
    testLogAtPos pos ("computing type of " ++ value) $ do
        integral <- testLog ("checking if type " ++ value ++ " is an integer") $ do
            success <- runCompileBooleanTest z $ "(" ++ value ++ ")(int)(" ++ value ++ ")1.4 == (" ++ value ++ ")1.4"
            testLog' $ "result: " ++ (if success then "integer" else "pointer or floating")
            return success
        typeRet <- if integral
         then do
            signed <- testLog ("checking if type " ++ value ++ " is signed") $ do
                success <- runCompileBooleanTest z $ "(" ++ value ++ ")(-1) < (" ++ value ++ ")0"
                testLog' $ "result: " ++ (if success then "signed" else "unsigned")
                return success
            size <- computeConst z ("sizeof(" ++ value ++ ")")
            return $ (if signed then "Int" else "Word") ++ (show (size * 8))
         else do
            pointer <- testLog ("checking if type " ++ value ++ " is a pointer") $ do
                success <- runCompileIsPointerTest z value
                testLog' $ "result: " ++ (if success then "pointer" else "floating")
                return success
            if pointer
                then return "CUIntPtr"
                else do
                    let checkSize test = testLog ("checking if " ++ test) $ do
                            success <- runCompileBooleanTest z test
                            testLog' $ "result: " ++ show success
                            return success
                    ldouble <- checkSize ("sizeof(" ++ value ++ ") > sizeof(double)")
                    if ldouble
                    then return "LDouble"
                    else do
                        double <- checkSize ("sizeof(" ++ value ++ ") == sizeof(double)")
                        if double
                        then return "Double"
                        else return "Float"
        testLog' $ "result: " ++ typeRet
        return typeRet
computeType _ = error "computeType argument isn't a Special"

outHeaderCProg' :: Token -> String
outHeaderCProg' (Special pos key value) = outHeaderCProg (pos,key,value)
outHeaderCProg' _ = ""

-- Checks if an #if/#ifdef etc. etc. is true by inserting a #error
-- and seeing if the compile fails.
checkConditional :: ZCursor Token -> TestMonad Bool
checkConditional (ZCursor s@(Special pos key value) above below) = do
    config <- testGetConfig
    flags <- testGetFlags
    let test = outTemplateHeaderCProg (cTemplate config) ++
               (concatMap outFlagHeaderCProg flags) ++
               (concatMap outHeaderCProg' above) ++
               outHeaderCProg' s ++ "#error T\n" ++
               (concatMap outHeaderCProg' below)
    testLogAtPos pos ("checking #" ++ key ++ " " ++ value) $ do
        condTrue <- not `fmap` runCompileTest test
        testLog' $ "result: " ++ show condTrue
        return condTrue
checkConditional _ = error "checkConditional argument isn't a Special"

-- Make sure the value we're trying to binary search isn't floating point.
checkValueIsIntegral :: ZCursor Token -> Bool -> TestMonad Bool
checkValueIsIntegral z@(ZCursor (Special _ _ value) _ _) nonNegative = do
    let intType = if nonNegative then "unsigned long long" else "long long"
    testLog ("checking if " ++ value ++ " is an integer") $ do
        success <- runCompileBooleanTest z $ "(" ++ intType ++ ")(" ++ value ++ ") == (" ++ value ++ ")"
        testLog' $ "result: " ++ (if success then "integer" else "floating")
        return success
checkValueIsIntegral _ _ = error "checkConditional argument isn't a Special"

compareConst :: ZCursor Token -> IntegerComparison -> TestMonad Bool
compareConst z@(ZCursor (Special _ _ value) _ _) cmpTest = do
    testLog ("checking " ++ value ++ " " ++ show cmpTest) $ do
        success <- runCompileBooleanTest z $ "(" ++ value ++ ") " ++ cShowCmpTest cmpTest
        testLog' $ "result: " ++ show success
        return success
compareConst _ _ = error "compareConst argument isn't a Special"

-- Given a compile-time constant with boolean type, this extracts the
-- value of the constant by compiling a .c file only.
--
-- The trick comes from autoconf: use the fact that the compiler must
-- perform constant arithmetic for computation of array dimensions, and
-- will generate an error if the array has negative size.
runCompileBooleanTest :: ZCursor Token -> String -> TestMonad Bool
runCompileBooleanTest (ZCursor s above below) booleanTest = do
    config <- testGetConfig
    flags <- testGetFlags
    let test = -- all the surrounding code
               outTemplateHeaderCProg (cTemplate config) ++
               (concatMap outFlagHeaderCProg flags) ++
               (concatMap outHeaderCProg' above) ++
               outHeaderCProg' s ++
               -- the test
               "int _hsc2hs_test() {\n" ++
               "  static int test_array[1 - 2 * !(" ++ booleanTest ++ ")];\n" ++
               "  return test_array[0];\n" ++
               "}\n" ++
               (concatMap outHeaderCProg' below)
    runCompileTest test

runCompileIsPointerTest :: ZCursor Token -> String -> TestMonad Bool
runCompileIsPointerTest (ZCursor s above below) ty = do
    config <- testGetConfig
    flags <- testGetFlags
    let test = -- all the surrounding code
               outTemplateHeaderCProg (cTemplate config) ++
               (concatMap outFlagHeaderCProg flags) ++
               (concatMap outHeaderCProg' above) ++
               outHeaderCProg' s ++
               -- the test
               "void *_hsc2hs_test(" ++ ty ++ " val) {\n" ++
               "  return val;\n" ++
               "}\n" ++
               (concatMap outHeaderCProg' below)
    runCompileTest test

runCompileAsmIntegerTest :: ZCursor Token -> TestMonad Integer
runCompileAsmIntegerTest (ZCursor s@(Special _ _ value) above below) = do
    config <- testGetConfig
    flags <- testGetFlags
    let key = "___hsc2hs_int_test"
    let test = -- all the surrounding code
               outTemplateHeaderCProg (cTemplate config) ++
               (concatMap outFlagHeaderCProg flags) ++
               (concatMap outHeaderCProg' above) ++
               outHeaderCProg' s ++
               -- the test
               "extern unsigned long long ___hsc2hs_BOM___;\n" ++
               "unsigned long long ___hsc2hs_BOM___ = 0x100000000;\n" ++
               "extern unsigned long long " ++ key ++ "___hsc2hs_sign___;\n" ++
               "unsigned long long " ++ key ++ "___hsc2hs_sign___ = (" ++ value ++ ") < 0;\n" ++
               "extern unsigned long long " ++ key ++ ";\n" ++
               "unsigned long long " ++ key ++ " = (" ++ value ++ ");\n"++
               (concatMap outHeaderCProg' below)
    runCompileExtract key test
runCompileAsmIntegerTest _ = error "runCompileAsmIntegerTestargument isn't a Special"

runCompileExtract :: String -> String -> TestMonad Integer
runCompileExtract k testStr = do
    makeTest3 (".c", ".s", ".txt") $ \(cFile, sFile, stdout) -> do
      liftTestIO $ writeBinaryFile cFile testStr
      flags <- testGetFlags
      compiler <- testGetCompiler
      -- -g0 suppresses debug/DWARF sections that produce assembly
      -- directives the ATT parser cannot handle.
      _ <- runCompiler compiler
                  (["-S", "-c", "-g0", cFile, "-o", sFile] ++ [f | CompFlag f <- flags])
                  (Just stdout)
      asm <- liftTestIO $ ATT.parse sFile
      return $ fromMaybe (error "Failed to extract integer") (ATT.lookupInteger k asm)

runCompileTest :: String -> TestMonad Bool
runCompileTest testStr = do
    makeTest3 (".c", ".o",".txt") $ \(cFile,oFile,stdout) -> do
      liftTestIO $ writeBinaryFile cFile testStr
      flags <- testGetFlags
      compiler <- testGetCompiler
      runCompiler compiler
                  (["-c",cFile,"-o",oFile]++[f | CompFlag f <- flags])
                  (Just stdout)

runCompiler :: FilePath -> [String] -> Maybe FilePath -> TestMonad Bool
runCompiler prog args mStdoutFile = do
  let cmdLine = showCommandForUser prog args
  testLog ("executing: " ++ cmdLine) $ liftTestIO $ do
      mHOut <- case mStdoutFile of
               Nothing -> return Nothing
               Just stdoutFile -> liftM Just $ openFile stdoutFile WriteMode
      process <- runProcess prog args Nothing Nothing Nothing mHOut mHOut
      case mHOut of
          Just hOut -> hClose hOut
          Nothing -> return ()
      exitStatus <- waitForProcess process
      return $ case exitStatus of
                 ExitSuccess -> True
                 ExitFailure _ -> False

-- The main driver for cross-compilation mode
outputCross :: Config -> String -> String -> String -> String -> [Token] -> IO ()
outputCross config outName outDir outBase inName toks =
    runTestMonad $ do
        -- Collect all batchable directives from the token stream
        let (entries, batchIdx) = collectBatchEntries toks

        -- Batch compile if enabled and there are batchable entries
        batch <- if cNoBatch config || null entries
                 then return emptyBatch
                 else do
                     results <- runBatchCompile entries toks
                     return (resolveBatch results batchIdx)

        -- Generate output using batch results for fast constant lookup
        file <- liftTestIO $ openFile outName WriteMode
        (diagnose batch inName (liftTestIO . hPutStr file) toks
           `testFinally` (liftTestIO $ hClose file))
           `testOnException` (liftTestIO $ removeFile outName) -- cleanup on errors
    where
    tmenv = TestMonadEnv (cVerbose config) 0 (cKeepFiles config) (outDir++outBase++"_hsc_test") (cFlags config) config (cCompiler config)
    runTestMonad x = runTest x tmenv 0 >>= (handleError . fst)

    handleError (Left e) = die (e++"\n")
    handleError (Right ()) = return ()
