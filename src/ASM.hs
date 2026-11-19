{-# LANGUAGE BangPatterns #-}
module ASM
    ( asmOverrideHeader
    , asmProbeAttrs
    , rawCompilerL
    , runCrossAsm
    , readAsmFile
    , parseAsmOps
    , decodeAsmChunks
    ) where

import Control.Exception (evaluate)
import Control.Monad (when)
import Data.Bits (shiftL, (.|.), (.&.))
import Data.Char (chr, isAlphaNum, isDigit, isSpace, toLower, toUpper)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.List (isPrefixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Word (Word64)
import Numeric (showHex, showOct)
import System.Directory (removeFile)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.IO (IOMode(ReadMode), char8, hGetContents, hPutStrLn, hSetEncoding, stderr, withFile)
import System.Process (CreateProcess(..), StdStream(..), createProcess, proc, waitForProcess)

import Common
import Compat.ResponseFile (escapeArgs)
import Flags

-- | Target C ABI byte widths reported by `@HSC@ABI` (defaults to LP64).
data AbiWidths = AbiWidths
    { abiInt     :: !Int
    , abiLong    :: !Int
    , abiSizeT   :: !Int
    , abiPtrdiff :: !Int
    , abiPtr     :: !Int
    } deriving (Show)

defaultAbi :: AbiWidths
defaultAbi = AbiWidths 4 8 8 8 8

data AsmVal
    = VInt !Integer !Word64 !Bool
    | VStr !String
    deriving (Show)

data AsmOp
    = OpAbi !AbiWidths
    | OpChunkBegin !Int
    | OpChunkEnd   !Int
    | OpPrintfBegin
    | OpPrintfEnd
    | OpFputs
    | OpPutchar
    | OpConstStr
    | OpHaskellize
    | OpMangle
    | OpTypeMarkup
    | OpInt !Integer !Word64 !Bool
    | OpStrBegin !Int
    | OpStrBytes ![Int]
    | OpStrEnd
    deriving (Show)

-- | Function attributes placed on `void _hsc2hs_cross_probe(void)` in CrossCodegen.hs.
-- Ensures GCC unrolls nested struct/union descriptor loops (e.g. bindings-DSL)
-- even if user cFlags pass -O0 or conservative unroll thresholds.
asmProbeAttrs :: String
asmProbeAttrs = unlines
    [ "#if defined(__clang__)"
    , "__attribute__((used, noinline))"
    , "#elif defined(__GNUC__)"
    , "__attribute__((used, noinline, optimize(\"O2,unroll-loops\")))"
    , "#endif"
    ]

-- | Injected after `template-hsc.h` and user headers so all `hsc_*` macros
-- serialize their output into `.ascii "@HSC@..."` assembly records under `cc -S -O2`.
-- Note: CrossCodegen also emits `#define HSC2HS_ASM 1` at line 1 of `_hsc_make.c`
-- so headers like `<bindings.dsl.h>` can detect cross-ASM mode at `#include` time.
asmOverrideHeader :: String
asmOverrideHeader = unlines
    [ "#include <stdint.h>"
    , "#include <stddef.h>"
    , ""
    , "#ifndef typeof"
    , "#define typeof __typeof__"
    , "#endif"
    , ""
    , "#undef hsc_printf"
    , "#undef hsc_fputs"
    , "#undef hsc_putchar"
    , "#undef hsc_stdout"
    , "#undef hsc_const_str"
    , "#undef hsc_haskellize"
    , "#ifndef HSC2HS_ASM"
    , "#define HSC2HS_ASM 1"
    , "#endif"
    , ""
    , "#define HSC_RAW(s) __asm__ volatile (\"\\n.ascii \\\"@HSC@\" s \"\\\\n\\\"\\n\" ::: \"memory\")"
    , ""
    , "#define HSC_EMIT_ABI() __asm__ volatile ( \\"
    , "    \"\\n.ascii \\\"@HSC@ABI %[si] %[sl] %[sz] %[sp] %[spv]\\\\n\\\"\\n\" \\"
    , "    : : [si]\"i\"(sizeof(int)), [sl]\"i\"(sizeof(long)), \\"
    , "        [sz]\"i\"(sizeof(size_t)), [sp]\"i\"(sizeof(ptrdiff_t)), \\"
    , "        [spv]\"i\"(sizeof(void *)) \\"
    , "    : \"memory\")"
    , ""
    , "/* `0 ? (x) : (x)` decays char[] arrays to char* on GCC (class 14 -> class 5)"
    , " * and promotes bitfield lvalues cleanly before `__typeof__` inspects them. */"
    , "#define HSC_DECAY_T(x) __typeof__(0 ? (x) : (x))"
    , "#define HSC_IS_CHAR_PTR(x) ( \\"
    , "    __builtin_types_compatible_p(HSC_DECAY_T(x), const char *) || \\"
    , "    __builtin_types_compatible_p(HSC_DECAY_T(x), char *) )"
    , ""
    , "#define HSC_IS_PTR(x)  (__builtin_classify_type(0 ? (x) : (x)) == 5)"
    , "#define HSC_IS_FLT(x)  (__builtin_classify_type(0 ? (x) : (x)) == 8)"
    , "/* Do not cast through uintptr_t. That drops the array initializer, so"
    , " * clang 21's i386 and MinGW backends no longer treat __builtin_strlen"
    , " * as an \"i\" immediate. The bare expression keeps const char[] and"
    , " * string literals foldable; other types select the empty literal. */"
    , "#define HSC_AS_STR(x)  __builtin_choose_expr(HSC_IS_CHAR_PTR(x), (x), \"\")"
    , "#define HSC_AS_UINT(x) __builtin_choose_expr(HSC_IS_PTR(x), (uintptr_t)(x), 0ULL)"
    , ""
    , "#define HSC_AS_NUM(x) \\"
    , "    __builtin_choose_expr(HSC_IS_PTR(x), (uintptr_t)(x), \\"
    , "    __builtin_choose_expr(HSC_IS_FLT(x), 0, (x)))"
    , ""
    , "#define HSC_TO_U64(x) \\"
    , "    ((HSC_AS_NUM(x)) < 0 ? (uint64_t)(int64_t)(HSC_AS_NUM(x)) : (uint64_t)(HSC_AS_NUM(x)))"
    , ""
    , "/* Split 64-bit values into 32-bit halves so 32-bit targets (i686/arm/wasm32)"
    , " * never reject 64-bit \"i\" constraints and INT64_MIN never overflows. */"
    , "#define HSC_EMIT_INT(x) __asm__ volatile ( \\"
    , "    \"\\n.ascii \\\"@HSC@INT %[hi] %[lo] %[neg]\\\\n\\\"\\n\" \\"
    , "    : : [hi]  \"i\" ((uint32_t)(HSC_TO_U64(x) >> 32)), \\"
    , "        [lo]  \"i\" ((uint32_t)(HSC_TO_U64(x) & 0xffffffffULL)), \\"
    , "        [neg] \"i\" ((int)((HSC_AS_NUM(x)) < 0)) \\"
    , "    : \"memory\")"
    , ""
    , "/* Clamp index inside subscript so GCC never triggers -Warray-bounds or"
    , " * refuses to fold out-of-bounds reads on short literals like \"Int\"[7]."
    , " * `_hsc_n` is the length HSC_EMIT_STR just scanned. */"
    , "#define HSC_SB(s, i) \\"
    , "    ((size_t)(i) < _hsc_n \\"
    , "        ? (unsigned char)((s)[(size_t)(i) < _hsc_n ? (size_t)(i) : 0]) \\"
    , "        : 0U)"
    , ""
    , "#define HSC_S8(s, b) __asm__ volatile ( \\"
    , "    \"\\n.ascii \\\"@HSC@S8 %[b0] %[b1] %[b2] %[b3] %[b4] %[b5] %[b6] %[b7]\\\\n\\\"\\n\" \\"
    , "    : : [b0]\"i\"(HSC_SB(s,(b)+0)), [b1]\"i\"(HSC_SB(s,(b)+1)), \\"
    , "        [b2]\"i\"(HSC_SB(s,(b)+2)), [b3]\"i\"(HSC_SB(s,(b)+3)), \\"
    , "        [b4]\"i\"(HSC_SB(s,(b)+4)), [b5]\"i\"(HSC_SB(s,(b)+5)), \\"
    , "        [b6]\"i\"(HSC_SB(s,(b)+6)), [b7]\"i\"(HSC_SB(s,(b)+7))  \\"
    , "    : \"memory\")"
    , ""
    , "#define HSC_S64(s, b) do { \\"
    , "    if (_hsc_n > (b)+0)  HSC_S8(s, (b)+0);  if (_hsc_n > (b)+8)  HSC_S8(s, (b)+8);  \\"
    , "    if (_hsc_n > (b)+16) HSC_S8(s, (b)+16); if (_hsc_n > (b)+24) HSC_S8(s, (b)+24); \\"
    , "    if (_hsc_n > (b)+32) HSC_S8(s, (b)+32); if (_hsc_n > (b)+40) HSC_S8(s, (b)+40); \\"
    , "    if (_hsc_n > (b)+48) HSC_S8(s, (b)+48); if (_hsc_n > (b)+56) HSC_S8(s, (b)+56); \\"
    , "} while (0)"
    , ""
    , "/* A literal's __builtin_strlen is an integer constant. A pointer that"
    , " * becomes a literal only after stores are propagated is lowered to a"
    , " * libc strlen under -ffreestanding, which is not an \"i\" immediate, so"
    , " * that case scans bytes instead. */"
    , "#define HSC_EMIT_STR(s) do { \\"
    , "    size_t _hsc_n; \\"
    , "    const char *_hsc_s; \\"
    , "    if (__builtin_constant_p(__builtin_strlen(s))) { \\"
    , "        _hsc_n = __builtin_strlen(s); \\"
    , "        _hsc_s = (const char *)(s); \\"
    , "    } else { \\"
    , "        _hsc_s = (const char *)(s); \\"
    , "        _hsc_n = 0; \\"
    , "        while (_hsc_n < 512 && _hsc_s[_hsc_n] != 0) _hsc_n++; \\"
    , "    } \\"
    , "    if (_hsc_n == 512 && _hsc_s[512] != 0) \\"
    , "        __asm__ volatile (\".error \\\"hsc2hs string > 512 bytes\\\"\"); \\"
    , "    __asm__ volatile (\"\\n.ascii \\\"@HSC@STR_BEGIN %[n]\\\\n\\\"\\n\" :: [n]\"i\"(_hsc_n) : \"memory\"); \\"
    , "    HSC_S64(_hsc_s, 0);   HSC_S64(_hsc_s, 64);  HSC_S64(_hsc_s, 128); HSC_S64(_hsc_s, 192); \\"
    , "    HSC_S64(_hsc_s, 256); HSC_S64(_hsc_s, 320); HSC_S64(_hsc_s, 384); HSC_S64(_hsc_s, 448); \\"
    , "    HSC_RAW(\"STR_END\"); \\"
    , "} while (0)"
    , ""
    , "/* A non-constant address (const char[], or a field pointer stored from"
    , " * a literal) takes the string arm. The bare expression keeps the"
    , " * initializer; a uintptr_t cast makes i386 reject the bytes. A null"
    , " * char* has a constant address and a non-constant length, so it takes"
    , " * the integer arm (%p null, not a string). */"
    , "#define HSC_ARG(x) do { \\"
    , "    if (HSC_IS_CHAR_PTR(x) && !__builtin_constant_p((uintptr_t)(x))) \\"
    , "        HSC_EMIT_STR(HSC_AS_STR(x)); \\"
    , "    else if (HSC_IS_CHAR_PTR(x) && __builtin_constant_p(__builtin_strlen(HSC_AS_STR(x)))) \\"
    , "        HSC_EMIT_STR(HSC_AS_STR(x)); \\"
    , "    else \\"
    , "        HSC_EMIT_INT(x); \\"
    , "} while (0)"
    , ""
    , "#define HSC_FE0()"
    , "#define HSC_FE1(a)      HSC_ARG(a)"
    , "#define HSC_FE2(a, ...) HSC_ARG(a); HSC_FE1(__VA_ARGS__)"
    , "#define HSC_FE3(a, ...) HSC_ARG(a); HSC_FE2(__VA_ARGS__)"
    , "#define HSC_FE4(a, ...) HSC_ARG(a); HSC_FE3(__VA_ARGS__)"
    , "#define HSC_FE5(a, ...) HSC_ARG(a); HSC_FE4(__VA_ARGS__)"
    , "#define HSC_FE6(a, ...) HSC_ARG(a); HSC_FE5(__VA_ARGS__)"
    , "#define HSC_FE7(a, ...) HSC_ARG(a); HSC_FE6(__VA_ARGS__)"
    , "#define HSC_FE8(a, ...) HSC_ARG(a); HSC_FE7(__VA_ARGS__)"
    , "#define HSC_PICK(_0,_1,_2,_3,_4,_5,_6,_7,_8,N,...) N"
    , "#define HSC_ARGS(...) HSC_PICK(_0, ##__VA_ARGS__, \\"
    , "    HSC_FE8, HSC_FE7, HSC_FE6, HSC_FE5, HSC_FE4, HSC_FE3, HSC_FE2, HSC_FE1, HSC_FE0)(__VA_ARGS__)"
    , ""
    , "#define hsc_stdout()       ((void *)0)"
    , "#define hsc_printf(fmt, ...) do { \\"
    , "    HSC_RAW(\"PRINTF_BEGIN\"); HSC_EMIT_STR(fmt); HSC_ARGS(__VA_ARGS__); HSC_RAW(\"PRINTF_END\"); \\"
    , "} while (0)"
    , "#define hsc_fputs(s, fp)   do { (void)(fp); HSC_RAW(\"FPUTS\"); HSC_EMIT_STR(s); } while (0)"
    , "#define hsc_putchar(c)     do { HSC_RAW(\"PUTCHAR\"); HSC_EMIT_INT((unsigned char)(c)); } while (0)"
    , "#define hsc_const_str(s)   do { HSC_RAW(\"CONST_STR\"); HSC_EMIT_STR(s); } while (0)"
    , "#define hsc_haskellize(s)  do { HSC_RAW(\"HASKELLIZE\"); HSC_EMIT_STR(s); } while (0)"
    , "#define hsc_mangle(pfx, s) do { HSC_RAW(\"MANGLE\"); HSC_EMIT_STR(pfx); HSC_EMIT_STR(s); } while (0)"
    , "/* bindings-dsl `<ident>` becomes `C'ident` in the decoder. The C side"
    , " * only emits the spelling, so the bytes stay an \"i\" immediate. */"
    , "#define hsc_typemarkup(s) do { HSC_RAW(\"TYPEMARKUP\"); HSC_EMIT_STR(s); } while (0)"
    , ""
    , "#define HSC_CHUNK_BEGIN(id) __asm__ volatile (\"\\n.ascii \\\"@HSC@CHUNK_BEGIN %[i]\\\\n\\\"\\n\" :: [i]\"i\"(id) : \"memory\")"
    , "#define HSC_CHUNK_END(id)   __asm__ volatile (\"\\n.ascii \\\"@HSC@CHUNK_END %[i]\\\\n\\\"\\n\"   :: [i]\"i\"(id) : \"memory\")"
    ]

-- | Invoke the C compiler, spilling arguments to a GNU/Clang `@response` file
-- whenever the command line >= 16 KiB (avoiding Win32's 32 KiB CreateProcessW
-- limit) or when `HSC2HS_FORCE_RSP=1` is set in the environment (for testing).
rawCompilerL :: String -> Config -> FilePath -> [String] -> IO ()
rawCompilerL action config rspPath args = do
    forceRsp <- (== Just "1") <$> lookupEnv "HSC2HS_FORCE_RSP"
    let cmdLen = sum (map ((+ 1) . length) args)
        useRsp = forceRsp || cmdLen >= 16384
        progArgs = if useRsp then ["@" ++ rspPath] else args
    when useRsp $ writeBinaryFile rspPath (escapeArgs args)
    when (cVerbose config) $
        hPutStrLn stderr $
            "Executing: " ++ cCompiler config ++ " " ++ unwords args
            ++ (if useRsp then " (@" ++ rspPath ++ ")" else "")
    runCompiler action (cCompiler config) progArgs args rspPath
    when (useRsp && not (cKeepFiles config)) $ removeFile rspPath

-- | Run `cc` with an argument vector. `shownArgs` is the un-spilled command,
-- recorded in the failure message. Response-file spilling is decided by
-- `rawCompilerL`; this does not go through `Common.rawSystemL`, which always
-- invents its own temporary response file.
runCompiler :: String -> FilePath -> [String] -> [String] -> FilePath -> IO ()
runCompiler action compiler progArgs shownArgs rspPath = do
    (_ ,_ ,progerr ,ph) <- createProcess (proc compiler progArgs)
        { std_err = CreatePipe }
    errdata <- maybeReadHandle progerr
    exitStatus <- waitForProcess ph
    case exitStatus of
        ExitFailure exitCode ->
            die $ action ++ " failed "
                ++ "(exit code " ++ show exitCode ++ ")\n"
                ++ "rsp file was: " ++ show rspPath ++ "\n"
                ++ "command was: " ++ compiler ++ " " ++ unwords shownArgs ++ "\n"
                ++ "error: " ++ errdata ++ "\n"
        _ -> return ()

-- | Strictly read a `.s` assembly file using `char8` (ISO-8859-1) encoding so:
--   1. Non-ASCII/non-UTF-8 bytes in `.file`/`.ident` directives never fail
--      under `LC_ALL=C` (Nix/Docker) or Windows multi-byte codepages; and
--   2. The file handle is strictly closed before `removeFile_` runs on Windows.
readAsmFile :: FilePath -> IO String
readAsmFile path = withFile path ReadMode $ \h -> do
    hSetEncoding h char8
    s <- hGetContents h
    _ <- evaluate (length s)
    return s

-- | Invoke target C compiler once with `-S -O2` and decode all `@HSC@` chunks.
runCrossAsm :: Config -> FilePath -> FilePath -> String -> IO (Map Int String)
runCrossAsm config outCName outSName cProg = do
    let rspName = outCName ++ ".rsp"
    writeBinaryFile outCName cProg
    rawCompilerL ("compiling " ++ outCName) config rspName
        (  ["-S"]
        ++ [f | CompFlag f <- cFlags config]
        ++ ["-O2", outCName, "-o", outSName]
        )
    asmText <- readAsmFile outSName
    case decodeAsmChunks (parseAsmOps asmText) of
        Left err      -> die ("hsc2hs: assembly decode error: " ++ err ++ "\n")
        Right (_, mp) -> return mp

-- ---------------------------------------------------------------------------
-- Scraping & decoding `@HSC@...` records
-- ---------------------------------------------------------------------------

parseAsmOps :: String -> [AsmOp]
parseAsmOps = concatMap extractFromLine . lines
  where
    marker = "@HSC@"

    extractFromLine [] = []
    extractFromLine s  = case findMarker s of
        Nothing -> []
        Just afterMarker ->
            let (payload, rest) = spanPayload afterMarker
            in case parsePayload (words payload) of
                Just op -> op : extractFromLine rest
                Nothing -> extractFromLine rest

    findMarker [] = Nothing
    findMarker s@(_:xs)
        | marker `isPrefixOf` s = Just (drop (length marker) s)
        | otherwise             = findMarker xs

    spanPayload []                      = ([], [])
    spanPayload ('"':rest)              = ([], rest)
    spanPayload ('\\':'n':rest)         = ([], rest)
    spanPayload ('\\':'r':rest)         = ([], rest)
    spanPayload ('\\':'0':'1':'2':rest) = ([], rest)
    spanPayload ('\\':'0':rest)         = ([], rest)
    spanPayload (c:cs)                  = let (p, r) = spanPayload cs in (c:p, r)

    imm :: String -> Integer
    imm s = case dropWhile (\c -> c == '$' || c == '#' || isSpace c) s of
        ('-':ds) -> negate (read (takeWhile isDigit ds))
        ds       -> read (takeWhile isDigit ds)

    parsePayload ("ABI":si:sl:sz:sp:spv:_) =
        Just $ OpAbi AbiWidths
            { abiInt     = fromInteger (imm si)
            , abiLong    = fromInteger (imm sl)
            , abiSizeT   = fromInteger (imm sz)
            , abiPtrdiff = fromInteger (imm sp)
            , abiPtr     = fromInteger (imm spv)
            }
    parsePayload ("CHUNK_BEGIN":i:_) = Just (OpChunkBegin (fromInteger (imm i)))
    parsePayload ("CHUNK_END":i:_)   = Just (OpChunkEnd   (fromInteger (imm i)))
    parsePayload ("PRINTF_BEGIN":_)  = Just OpPrintfBegin
    parsePayload ("PRINTF_END":_)    = Just OpPrintfEnd
    parsePayload ("FPUTS":_)         = Just OpFputs
    parsePayload ("PUTCHAR":_)       = Just OpPutchar
    parsePayload ("CONST_STR":_)     = Just OpConstStr
    parsePayload ("HASKELLIZE":_)    = Just OpHaskellize
    parsePayload ("MANGLE":_)        = Just OpMangle
    parsePayload ("TYPEMARKUP":_)    = Just OpTypeMarkup
    parsePayload ("STR_BEGIN":n:_)   = Just (OpStrBegin (fromInteger (imm n)))
    parsePayload ("S8":bs)           = Just (OpStrBytes (map (fromInteger . imm) (take 8 bs)))
    parsePayload ("STR_END":_)       = Just OpStrEnd
    parsePayload ("INT":hi:lo:neg:_) =
        let !u64   = (fromInteger (imm hi) `shiftL` 32) .|. fromInteger (imm lo) :: Word64
            !isNeg = imm neg /= 0
            !sVal  = if isNeg
                        then toInteger (fromIntegral u64 :: Int64)
                        else toInteger u64
        in Just (OpInt sVal u64 isNeg)
    parsePayload _ = Nothing

decodeAsmChunks :: [AsmOp] -> Either String (AbiWidths, Map Int String)
decodeAsmChunks = goTop defaultAbi Map.empty
  where
    goTop !abi !acc [] = Right (abi, acc)
    goTop _    !acc (OpAbi abi' : ops) = goTop abi' acc ops
    goTop !abi !acc (OpChunkBegin cid : ops) = do
        (out, rest) <- goChunk abi cid [] ops
        goTop abi (Map.insertWith (++) cid out acc) rest
    goTop !abi !acc (_ : ops) = goTop abi acc ops

    goChunk _ cid !buf (OpChunkEnd cid' : rest)
        | cid == cid' = Right (concat (reverse buf), rest)
        | otherwise   = Left ("mismatched CHUNK_END " ++ show cid' ++ " inside " ++ show cid)
    goChunk abi cid !buf (OpPrintfBegin : ops) = do
        (vFmt, ops1) <- readVal ops
        fmt          <- expectStr "printf format" vFmt
        (args, ops2) <- readPrintfArgs [] ops1
        rendered     <- formatPrintf abi fmt args
        goChunk abi cid (rendered : buf) ops2
    goChunk abi cid !buf (OpFputs : ops) = do
        (v, ops1) <- readVal ops
        s         <- expectStr "fputs" v
        goChunk abi cid (s : buf) ops1
    goChunk abi cid !buf (OpPutchar : ops) = do
        (v, ops1) <- readVal ops
        case v of
            VInt _ u _ -> goChunk abi cid ([chr (fromInteger (toInteger (u .&. 0xff)))] : buf) ops1
            _          -> Left "putchar expected integer"
    goChunk abi cid !buf (OpConstStr : ops) = do
        (v, ops1) <- readVal ops
        s         <- expectStr "const_str" v
        goChunk abi cid (formatConstStr s : buf) ops1
    goChunk abi cid !buf (OpHaskellize : ops) = do
        (v, ops1) <- readVal ops
        s         <- expectStr "haskellize" v
        goChunk abi cid (haskellize s : buf) ops1
    goChunk abi cid !buf (OpMangle : ops) = do
        (vPfx, ops1) <- readVal ops
        (vStr, ops2) <- readVal ops1
        pfx <- expectStr "mangle prefix" vPfx
        s   <- expectStr "mangle ident"  vStr
        goChunk abi cid ((pfx ++ sanitizeBindings s) : buf) ops2
    goChunk abi cid !buf (OpTypeMarkup : ops) = do
        (v, ops1) <- readVal ops
        s         <- expectStr "typemarkup" v
        goChunk abi cid (markupType s : buf) ops1
    goChunk _ cid _ [] = Left ("unterminated CHUNK_BEGIN " ++ show cid)
    goChunk _ _ _ (op : _) = Left ("unexpected op inside chunk: " ++ show op)

    expectStr _   (VStr s) = Right s
    expectStr ctx v        = Left (ctx ++ ": expected VStr, got " ++ show v)

    readPrintfArgs !acc (OpPrintfEnd : rest) = Right (reverse acc, rest)
    readPrintfArgs !acc ops = do
        (v, rest) <- readVal ops
        readPrintfArgs (v : acc) rest

    readVal (OpInt s u n : rest)  = Right (VInt s u n, rest)
    readVal (OpStrBegin n : rest) = readStr n [] rest
    readVal ops = Left ("expected value record, got: " ++ show (take 3 ops))

    readStr len !acc (OpStrBytes bs : rest) = readStr len (acc ++ bs) rest
    readStr len !acc (OpStrEnd : rest)      = Right (VStr (map chr (take len acc)), rest)
    readStr _ _ ops = Left ("malformed string record near: " ++ show (take 3 ops))

formatConstStr :: String -> String
formatConstStr s = "\"" ++ go s ++ "\""
  where
    go [] = ""
    go ('"':cs)  = "\\\"" ++ go cs
    go ('\\':cs) = "\\\\" ++ go cs
    go (c:cs)
        | c >= ' ' && c <= '~' = c : go cs
        | otherwise =
            let guard = case cs of { (d:_) | isDigit d -> "\\&"; _ -> "" }
            in '\\' : show (fromEnum c) ++ guard ++ go cs

-- Match template-hsc.h `hsc_haskellize`: the first byte is always
-- lowercased and does not arm the "upper" flag. A leading '_' therefore
-- yields `_tsLeading`, not `_TsLeading`. Later '_' bytes are dropped and
-- arm uppercasing of the next byte.
haskellize :: String -> String
haskellize [] = []
haskellize (c0:cs0) = toLower c0 : go False cs0
  where
    go _ []          = []
    go _ ('_':cs)    = go True cs
    go True  (c:cs)  = toUpper c : go False cs
    go False (c:cs)  = toLower c : go False cs

-- | Rewrite bindings-dsl type spellings the way non-asm `bc_typemarkup`
-- does. `<ident>` becomes `C'` plus the last space-or-tab-separated token
-- inside the brackets. The brackets themselves are not copied. A span with
-- no closing `>` still rewrites, and an empty span copies nothing.
markupType :: String -> String
markupType = go
  where
    go [] = []
    go cs =
        let (pre, rest) = break (== '<') cs
        in case rest of
            [] -> pre
            (_:afterLt) ->
                let (inside, rest2) = break (== '>') afterLt
                    piece = case lastWsToken inside of
                        ""  -> ""
                        tok -> "C'" ++ tok
                in case rest2 of
                    []          -> pre ++ piece
                    (_:afterGt) -> pre ++ piece ++ go afterGt

    lastWsToken s = finish (foldl step ("", []) s)
      where
        step (prev, cur) c
            | c == ' ' || c == '\t' =
                if null cur then (prev, []) else (reverse cur, [])
            | otherwise = (prev, c:cur)
        finish (prev, [])  = prev
        finish (_, cur)    = reverse cur

sanitizeBindings :: String -> String
sanitizeBindings s =
    let stripped = case words s of
            ("struct":rest) -> unwords rest
            ("union":rest)  -> unwords rest
            ("enum":rest)   -> unwords rest
            _               -> s
    in [ if isAlphaNum c || c == '\'' then c else '_' | c <- stripped ]

maskUnsigned :: Int -> Word64 -> Word64
maskUnsigned bytes u = case bytes of
    1 -> u .&. 0xff
    2 -> u .&. 0xffff
    4 -> u .&. 0xffffffff
    _ -> u

maskSigned :: Int -> Word64 -> Integer
maskSigned bytes u = case bytes of
    1 -> toInteger (fromIntegral u :: Int8)
    2 -> toInteger (fromIntegral u :: Int16)
    4 -> toInteger (fromIntegral u :: Int32)
    _ -> toInteger (fromIntegral u :: Int64)

modWidth :: AbiWidths -> String -> Int
modWidth abi m = case m of
    "hh" -> 1
    "h"  -> 2
    ""   -> abiInt abi
    "l"  -> abiLong abi
    "ll" -> 8
    "j"  -> 8
    "z"  -> abiSizeT abi
    "t"  -> abiPtrdiff abi
    _    -> 8

formatPrintf :: AbiWidths -> String -> [AsmVal] -> Either String String
formatPrintf abi = go
  where
    go [] _ = Right ""
    go ('%':'%':cs) args = ('%' :) <$> go cs args
    go ('%':cs) (arg:args) = do
        let (flags, cs1)  = span (`elem` "-+ #0") cs
            (widthS, cs2) = span isDigit cs1
            (_precS, cs3) = case cs2 of { ('.':r) -> span isDigit r; _ -> ("", cs2) }
            (lenMod, cs4) = span (`elem` "hljztL") cs3
        case cs4 of
            [] -> Left "truncated printf format string"
            (conv:rest) -> do
                piece <- renderSpec flags widthS lenMod conv arg
                (piece ++) <$> go rest args
    go ('%':_) [] = Left "insufficient arguments for hsc_printf format"
    go (c:cs) args = (c :) <$> go cs args

    renderSpec flags widthS lenMod conv arg = do
        let bytes = modWidth abi lenMod
        raw <- case (conv, arg) of
            ('s', VStr s)     -> Right s
            ('c', VInt _ u _) -> Right [chr (fromInteger (toInteger (u .&. 0xff)))]
            ('d', VInt _ u _) -> Right (show (maskSigned bytes u))
            ('i', VInt _ u _) -> Right (show (maskSigned bytes u))
            ('u', VInt _ u _) -> Right (show (maskUnsigned bytes u))
            ('x', VInt _ u _) ->
                let u' = maskUnsigned bytes u
                in Right ((if '#' `elem` flags && u' /= 0 then "0x" else "") ++ showHex u' "")
            ('X', VInt _ u _) ->
                let u' = maskUnsigned bytes u
                in Right ((if '#' `elem` flags && u' /= 0 then "0X" else "") ++ map toUpper (showHex u' ""))
            ('o', VInt _ u _) ->
                let u' = maskUnsigned bytes u
                in Right ((if '#' `elem` flags && u' /= 0 then "0" else "") ++ showOct u' "")
            ('p', VInt _ u _) ->
                let u' = maskUnsigned (abiPtr abi) u
                in Right (if u' == 0 then "0x0" else "0x" ++ showHex u' "")
            _ -> Left ("unsupported printf conversion %" ++ lenMod ++ [conv])
        let w = if null widthS then 0 else read widthS
            padChar = if '0' `elem` flags && '-' `notElem` flags then '0' else ' '
            pad = replicate (max 0 (w - length raw)) padChar
        Right $ if '-' `elem` flags then raw ++ pad else pad ++ raw
