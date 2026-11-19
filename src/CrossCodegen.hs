module CrossCodegen
    ( outputCross
    ) where

import Control.Exception (IOException, catch)
import Control.Monad (when)
import Data.Char (isAlphaNum, toUpper)
import Data.Foldable (foldl')
import Data.Map.Strict (lookup)
import Prelude hiding (lookup)
import System.Directory (removeFile)
import System.Exit (ExitCode(..), exitWith)

import ASM (asmOverrideHeader, asmProbeAttrs, runCrossAsm)
import C
import Common
import Flags
import HSCParser

-- | Generate Haskell without linking or running a target binary.
--
-- The probe is the same statement sequence 'DirectCodegen' puts in `main`,
-- so `#if` / `#ifdef` keep the same bytes. `outHsLine` on this pin emits a
-- C `hsc_line(...)` call; the Haskell `LINE` pragma is whatever that call
-- prints into the asm chunk. Source text goes out through `hsc_fputs`, and
-- `HSC_EMIT_STR` rejects a string longer than 512 bytes, so each fputs is
-- split at 400 bytes. The decoder concatenates them in order.
outputCross :: Config -> FilePath -> FilePath -> FilePath -> String -> [Token] -> IO ()
outputCross config outName outDir outBase inName toks = do
    let flags       = cFlags config
        cProgName   = outDir ++ outBase ++ "_hsc_make.c"
        sProgName   = outDir ++ outBase ++ "_hsc_make.s"
        outHFile    = outBase ++ "_hsc.h"
        outHName    = outDir ++ outHFile
        outCName    = outDir ++ outBase ++ "_hsc.c"
        specials    = [(pos, key, arg) | Special pos key arg <- toks]
        needsC      = any (\(_, key, _) -> key == "def") specials
        needsH      = needsC
        body        =
            outHeaderHs flags (if needsH then Just outHName else Nothing) specials
            ++ outHsLine (SourcePos inName 0 1)
            ++ fst (foldl' (outTokenCross (cColumn config)) (id, (True, True)) toks) ""
        cProg       = concat
            [ "#define HSC2HS_ASM 1\n"
            , outTemplateHeaderCProg (cTemplate config)
            , concatMap outFlagHeaderCProg flags
            , concatMap outHeaderCProg specials
            , asmOverrideHeader
            , "\n"
            , asmProbeAttrs
            , "void _hsc2hs_cross_probe(void) {\n"
            , "    HSC_EMIT_ABI();\n"
            , "    HSC_CHUNK_BEGIN(0);\n"
            , body
            , "    HSC_CHUNK_END(0);\n"
            , "}\n"
            ]
        includeGuard = map fixChar outHName
        fixChar c | isAlphaNum c = toUpper c
                  | otherwise    = '_'

    when (cNoCompile config) $ do
        writeBinaryFile cProgName cProg
        exitWith ExitSuccess

    chunkMap <- runCrossAsm config cProgName sProgName cProg
    case lookup 0 chunkMap of
        Nothing -> die "hsc2hs: cross probe emitted no @HSC@ chunk 0\n"
        Just hs -> writeBinaryFile outName hs

    when (not (cKeepFiles config)) $ do
        removeQuiet cProgName
        removeQuiet sProgName

    when needsH $ writeBinaryFile outHName $
        "#ifndef " ++ includeGuard ++ "\n" ++
        "#define " ++ includeGuard ++ "\n" ++
        "#include <HsFFI.h>\n" ++
        "#if __NHC__\n" ++
        "#undef HsChar\n" ++
        "#define HsChar int\n" ++
        "#endif\n" ++
        concatMap outFlagH flags ++
        concatMap outTokenH specials ++
        "#endif\n"

    when needsC $ writeBinaryFile outCName $
        "#include \"" ++ outHFile ++ "\"\n" ++
        concatMap outTokenC specials

-- | Same state machine as 'outTokenHs', but source text is split so each
-- `hsc_fputs` argument stays under the 512-byte `HSC_EMIT_STR` cap.
outTokenCross :: Bool -> (ShowS, (Bool, Bool)) -> Token -> (ShowS, (Bool, Bool))
outTokenCross enableCol (out, state) (Text pos txt) =
    (out . showString str, state')
  where
    (str, state') =
        outTextHs state pos txt outTextSplit outHsLine
            (if enableCol then outHsColumn else const "")
outTokenCross enableCol acc tok@(Special _ _ _) =
    -- Specials are short (`hsc_const`, `hsc_enum`, preprocessor lines).
    -- Delegate so the C statement and the (lineSync, colSync) update match
    -- direct mode exactly.
    outTokenHs enableCol acc tok

-- HSC_EMIT_STR rejects strlen > 512. A single source span in an `.hsc`
-- file is often longer. Pieces are concatenated by the decoder.
outTextSplit :: String -> String
outTextSplit = concatMap one . pieces
  where
    one p = "    hsc_fputs (\"" ++ showCString p ++ "\", hsc_stdout());\n"
    pieces s
        | null s    = []
        | otherwise = let (a, b) = splitAt 400 s in a : pieces b

removeQuiet :: FilePath -> IO ()
removeQuiet path = catch (removeFile path) handler
  where
    handler :: IOException -> IO ()
    handler _ = return ()
