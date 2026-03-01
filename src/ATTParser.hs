-- A rather crude asm parser.
--
--
-- we only handle a subset of AT&T assembly
-- right now.  This is what gcc and clang can
-- emit.  For clang using llvm-ir might be
-- even better.  For gcc gimple if that can
-- be consumed reliably somehow.
--
-- For now we'll rely on the at&t assembly
-- to be sufficient for constants.
--


module ATTParser where

import Control.Applicative ((<|>))
import Data.Word (Word32, Word64)
import Data.Int (Int64)
import Data.Char (isDigit, isSpace)
import Data.Bits (shiftL, shiftR, (.|.))
import Data.Maybe (fromMaybe)

data Inst = Ident String
          | Long Word32
          | Quad Word64
          | Ref String
          | Ascii String
          deriving Show

mkLong :: Word32 -> Inst
mkLong = Long
mkQuad :: Word64 -> Inst
mkQuad = Quad
-- | turn @x@ and @(x)@ into @Ref x@.
-- The (x) syntax can be found in mips assembly.
mkRef :: String -> Inst
mkRef ('(':r) | (')':r') <- reverse r = Ref $ reverse r'
mkRef r = Ref r

mkAscii :: String -> Inst
mkAscii = Ascii

type ASM = [(String, Inst)]

isIdent :: Inst -> Bool
isIdent (Ident _) = True
isIdent _ = False

trim :: String -> String
trim = reverse . dropWhile (`elem` " \t") . reverse . dropWhile (`elem` " \t")
-- | generalized @words@.
words' :: (a -> Bool) -> [a] -> [[a]]
words' p s = case dropWhile p s of
             [] -> []
             s' -> w : words' p s''
                   where (w, s'') = break p s'

isNumber :: String -> Bool
isNumber ('-':x) = all isDigit x
isNumber ('+':x) = all isDigit x
isNumber x       = all isDigit x

-- | process the assembly instructions, filtering out
-- identifiers and constant values.
--
-- Section directives are emitted as Ident nodes so that
-- filterDebugSections can track section boundaries and
-- discard instructions inside debug sections (e.g. COFF
-- CodeView .debug$S emitted by Clang on Windows even with -g0).
preprocess :: String -> [Inst]
preprocess [] = []
preprocess ('\t':attr) = let (h, t) = break isSpace attr
                         in case h:words' (=='\t') t of
                         -- Section directives: emit as Ident so
                         -- filterDebugSections can track them.
                         (".section":x:_)           -> [Ident (".section " ++ w x)]

                         -- 8 byte values
                         (".quad":x:_) | isNumber (w x) -> [mkQuad $ read (w x)]
                                       | otherwise      -> [mkRef  $ (w x)]
                         (".xword":x:_)| isNumber (w x) -> [mkQuad $ read (w x)]
                                       | otherwise      -> [mkRef  $ (w x)]
                         (".8byte":x:_)| isNumber (w x) -> [mkQuad $ read (w x)]
                                       | otherwise      -> [mkRef  $ (w x)]
                         ("data8":x:_) | isNumber (w x) -> [mkQuad $ read (w x)]
                                       | otherwise      -> [mkRef  $ (w x)]

                         -- 4 byte values
                         (".long":x:_) | isNumber (w x) -> [mkLong $ read (w x)]
                                       | otherwise      -> [mkRef  $ (w x)]
                         (".word":x:_) | isNumber (w x) -> [mkLong $ read (w x)]
                                       | otherwise      -> [mkRef  $ (w x)]
                         (".4byte":x:_)| isNumber (w x) -> [mkLong $ read (w x)]
                                       | otherwise      -> [mkRef  $ (w x)]

                         (".space":x:_)| (w x) == "4"   -> [mkLong 0]
                                       | (w x) == "8"   -> [mkQuad 0]
                         (".skip":x:_) | (w x) == "4"   -> [mkLong 0]
                                       | (w x) == "8"   -> [mkQuad 0]

                         (".ascii":x:_)             -> [mkAscii $ read x]
                         (".asciz":x:_)             -> [mkAscii $ read x ++ "\0"]
                         -- found on nios, sh4, alpha, mk68k; all without \0.
                         (".string":x:_)            -> [mkAscii $ read x ++ "\0"]
                         -- found on hppa
                         (".stringz":x:_)           -> [mkAscii $ read x ++ "\0"]
                         -- ia64
                         ("stringz":x:_)            -> [mkAscii $ read x ++ "\0"]
                         _                          -> []
  where
    w x = case words x of
      []     -> error $ "preprocess: expected some non-space characters, "
                     ++ "but got spaces only in '" ++ x ++ "'"
      hd : _ -> hd
preprocess ('.':'z':'e':'r':'o':'f':'i':'l':'l':' ':x) = case words' (==',') x of
      (_seg:_sect:sym:size:_) | size == "4" -> [Ident sym, mkLong 0]
                              | size == "8" -> [Ident sym, mkQuad 0]
      _ -> []
preprocess (c:cs) | not (isSpace c) = [Ident $ takeWhile (/= ':') (c:cs)]
                  | otherwise       = []

-- | turn the list of instructions into an associated list
parseInsts :: [Inst] -> [(String, Inst)]
parseInsts [] = []
parseInsts (Ident name:xs) = case break isIdent xs of
  ([], xs') -> parseInsts xs'
  (is, xs') -> (name, combineInst is):parseInsts xs'
parseInsts _ = error "Invalid instructions"

-- | combine instructions (e.g. two long into a quad)
-- Unknown patterns (e.g. debug section leftovers, WebAssembly metadata)
-- are mapped to a sentinel Quad 0 instead of a Ref, so that inlineRef
-- does not try to resolve a non-existent symbol.
combineInst :: [Inst] -> Inst
combineInst [Quad i] = Quad i
combineInst [Long i] = Quad (fromIntegral i)
combineInst [Long h, Long l] = Quad $ (shiftL (fromIntegral h) 32) .|. fromIntegral l
combineInst [Ref s]  = Ref s
combineInst [Ascii s] = Ascii s
combineInst _is = Quad 0  -- sentinel: unrecognized pattern, will not match lookups

-- | inline references
inlineRef :: [(String, Inst)] -> [(String, Inst)]
inlineRef xs = map go xs
  where go (k, Ref name) = (k, fromMaybe (error $ "failed to find reference " ++ show name) $ lookup name xs)
        go x = x

fixWordOrder :: [(String, Inst)] -> [(String, Inst)]
fixWordOrder xs = case lookupInteger "___hsc2hs_BOM___" xs of
  Just 1 -> map go xs
  _ -> xs
  where go (k, Quad w) = (k, Quad $ shiftL w 32 .|. shiftR w 32)
        go x = x

parse :: FilePath -> IO [(String, Inst)]
parse f = (fixWordOrder . inlineRef . parseInsts . filterDebugSections . concatMap preprocess . lines) `fmap` readFile f

-- | Filter out instructions that fall inside debug sections.
-- On Windows, Clang emits CodeView .debug$S sections even with -g0,
-- containing .long/.quad directives that confuse the parser. We track
-- section changes: when entering a debug section we drop all instructions
-- until the next non-debug section.
--
-- Section directives are emitted by preprocess as Ident nodes with names
-- like ".section .debug$S,\"dr\"" or ".section .text". Labels at column 0
-- (e.g. ".Ltmp0") also appear as Idents.
filterDebugSections :: [Inst] -> [Inst]
filterDebugSections = go False
  where
    go _       [] = []
    go inDebug (Ident name : rest)
      -- ".section .debug$S,..." or ".section .debug_info,..." → enter debug mode
      | isSectionDirective name && isDebugSectionName name = go True rest
      -- ".section .text,..." or ".section .data,..." → exit debug mode
      | isSectionDirective name = go False rest
      -- Column-0 section labels like ".text" or ".data" (no ".section" prefix)
      | isBareSectionLabel name = go False rest
      -- Normal label inside debug section → drop it
      | inDebug = go inDebug rest
      -- Normal label outside debug section → keep it
      | otherwise = Ident name : go False rest
    go True  (_:rest) = go True rest   -- drop data instructions in debug sections
    go False (x:rest) = x : go False rest

    -- Matches Ident nodes produced by the ".section" case in preprocess,
    -- which have the form ".section <section-name>"
    isSectionDirective s = take 9 s == ".section "

    -- Check if a .section directive names a debug section.
    isDebugSectionName s =
      let afterSection = drop 9 s  -- strip ".section " prefix
      in any (`isPrefixOf'` afterSection)
           [ ".debug$"  -- COFF CodeView (.debug$S, .debug$T)
           , ".debug_"  -- ELF DWARF (.debug_info, .debug_abbrev, etc.)
           ]

    -- Bare section labels at column 0 (e.g. ".text", ".data", ".bss")
    isBareSectionLabel s = s == ".text" || s == ".data" || s == ".bss"

    isPrefixOf' prefix str = take (length prefix) str == prefix

-- | lookup a symbol without or with underscore prefix
lookup_ :: String -> [(String,b)] -> Maybe b
lookup_ k l = lookup k l <|> lookup ("_" ++ k) l

lookupString :: String -> [(String, Inst)] -> Maybe String
lookupString k l = case (lookup_ k l) of
  Just (Ascii s) -> Just s
  _ -> Nothing

lookupInteger :: String -> [(String, Inst)] -> Maybe Integer
lookupInteger k l = case (lookup_ k l, lookup_ (k ++ "___hsc2hs_sign___") l) of
  (Just (Quad i), Just (Quad 1)) -> Just (fromIntegral (fromIntegral i :: Int64))
  (Just (Quad i), _) -> Just (fromIntegral i)
  _ -> Nothing
