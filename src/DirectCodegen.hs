{-# LANGUAGE CPP #-}
module DirectCodegen where

{-
The standard mode for hsc2hs: generates a C file which is
compiled and run; the output of that program is the .hs file.
-}

#if MIN_VERSION_base(4,6,0)
import Prelude hiding ( Foldable(..) )
#else
import Data.List ( foldl' )
#endif
import Data.Char                ( isAlphaNum, toUpper )
import Data.Foldable            ( Foldable(..) )
import Control.Monad            ( when )

import System.Directory         ( doesFileExist, removeFile )
import System.Exit              ( ExitCode(..), exitWith )
import System.FilePath          ( normalise )
import System.IO                ( IOMode(..), hClose, hPutStrLn, openFile, stderr )
import System.Process           ( CreateProcess(..), StdStream(..), createProcess
                                , proc, waitForProcess )

import C
import Common
import Flags
import HSCParser
import UtilsCodegen

outputDirect :: Config -> FilePath -> FilePath -> FilePath -> String -> [Token] -> IO ()
outputDirect config outName outDir outBase name toks = do

    let beVerbose    = cVerbose config
        flags        = cFlags config
        enableCol    = cColumn config
        cProgName    = outDir++outBase++"_hsc_make.c"
        oProgName    = outDir++outBase++"_hsc_make.o"
        progName     = outDir++outBase++"_hsc_make"
#if defined(mingw32_HOST_OS) || defined(__CYGWIN32__)
-- This is a real hack, but the quoting mechanism used for calling the C preprocesseor
-- via GHC has changed a few times, so this seems to be the only way...  :-P * * *
                          ++ ".exe"
#endif
        outHFile     = outBase++"_hsc.h"
        outHName     = outDir++outHFile
        outCName     = outDir++outBase++"_hsc.c"

    let execProgName
            | null outDir = normalise ("./" ++ progName)
            | otherwise   = progName

    let specials = [(pos, key, arg) | Special pos key arg <- toks]

    let needsC = any (\(_, key, _) -> key == "def") specials
        needsH = needsC
        possiblyRemove = if cKeepFiles config
                         then flip const
                         else finallyRemove

    let includeGuard = map fixChar outHName
            where
            fixChar c | isAlphaNum c = toUpper c
                      | otherwise    = '_'

    writeBinaryFile cProgName $
        outTemplateHeaderCProg (cTemplate config)++
        concatMap outFlagHeaderCProg flags++
        concatMap outHeaderCProg specials++
        "\nint main (void)\n{\n"++
        outHeaderHs flags (if needsH then Just outHName else Nothing) specials++
        outHsLine (SourcePos name 0 1)++
        fst (foldl' (outTokenHs enableCol) (id, (True, True)) toks) ""++
        "    return 0;\n}\n"

    when (cNoCompile config) $ exitWith ExitSuccess

    rawSystemL outDir outBase ("compiling " ++ cProgName) beVerbose
        (cCompiler config)
        (  ["-c"]
        ++ [cProgName]
        ++ ["-o", oProgName]
        ++ [f | CompFlag f <- flags]
        )
    possiblyRemove cProgName $
        withUtilsObject config outDir outBase $ \oUtilsName -> do

      rawSystemL outDir outBase ("linking " ++ oProgName) beVerbose
        (cLinker config)
        (  [oProgName, oUtilsName]
        ++ ["-o", progName]
        ++ [f | LinkFlag f <- flags]
        )
      possiblyRemove oProgName $ do

        actualProg <- resolveExecPath progName execProgName
        case cCrossRunner config of
            Nothing ->
                rawSystemWithStdOutL outDir outBase ("running " ++ actualProg)
                    beVerbose actualProg [] outName
            Just runnerStr -> case splitRunner runnerStr of
                [] -> die "hsc2hs: empty --cross-runner command\n"
                (rExe : rSplitArgs) ->
                    let extraArgs = [a | RunnerFlag a <- flags]
                        allArgs   = rSplitArgs ++ extraArgs ++ [actualProg]
                    -- Not rawSystemWithStdOutL: that always passes @response,
                    -- and a runner is not gcc. The wrapper must see its
                    -- arguments, including ones that contain spaces.
                    in runCaptured outName beVerbose rExe allArgs
        when (actualProg /= execProgName && not (cKeepFiles config)) $
            removeFile actualProg
        possiblyRemove progName $ do

          when needsH $ writeBinaryFile outHName $
            "#ifndef "++includeGuard++"\n" ++
            "#define "++includeGuard++"\n" ++
            "#include <HsFFI.h>\n" ++
            "#if __NHC__\n" ++
            "#undef HsChar\n" ++
            "#define HsChar int\n" ++
            "#endif\n" ++
            concatMap outFlagH flags++
            concatMap outTokenH specials++
            "#endif\n"

          when needsC $ writeBinaryFile outCName $
            "#include \""++outHFile++"\"\n"++
            concatMap outTokenC specials
            -- NB. outHFile not outHName; works better when processed
            -- by gcc or mkdependC.

-- Run the cross-runner with the real argument vector and capture stdout.
runCaptured :: FilePath -> Bool -> FilePath -> [String] -> IO ()
runCaptured outFile verbose exe args = do
    when verbose $
        hPutStrLn stderr $
            "Executing: " ++ unwords (exe : args) ++ " >" ++ outFile
    hOut <- openFile outFile WriteMode
    (_ ,_ ,progerr ,ph) <- createProcess (proc exe args)
        { std_out = UseHandle hOut
        , std_err = CreatePipe
        }
    errdata <- maybeReadHandle progerr
    exitStatus <- waitForProcess ph
    hClose hOut
    case exitStatus of
        ExitFailure exitCode ->
            die $ "running " ++ unwords (exe : args) ++ " failed "
                ++ "(exit code " ++ show exitCode ++ ")\n"
                ++ "output file:" ++ show outFile ++ "\n"
                ++ "error: " ++ errdata ++ "\n"
        _ -> return ()

-- MinGW cross-gcc on Unix writes `foo.exe` when `progName` has no suffix.
resolveExecPath :: FilePath -> FilePath -> IO FilePath
resolveExecPath rawP execP = do
    exists <- doesFileExist rawP
    if exists
        then return execP
        else do
            exeExists <- doesFileExist (rawP ++ ".exe")
            return (if exeExists then execP ++ ".exe" else execP)

-- Split `--cross-runner="qemu-aarch64 -L \"/my sysroot\""` on whitespace,
-- keeping quoted words intact.
splitRunner :: String -> [String]
splitRunner = goSkip
  where
    goSkip s = case dropWhile (`elem` " \t") s of
        [] -> []
        s' -> let (tok, rest) = goTok Nothing s' in tok : goSkip rest

    goTok _ [] = ("", "")
    goTok Nothing (c:cs)
        | c `elem` " \t" = ("", cs)
        | c == '"' || c == '\'' = goTok (Just c) cs
        | c == '\\', (x:xs) <- cs = let (t, r) = goTok Nothing xs in (x:t, r)
        | otherwise = let (t, r) = goTok Nothing cs in (c:t, r)
    goTok (Just q) (c:cs)
        | c == q = goTok Nothing cs
        | c == '\\', q == '"', (x:xs) <- cs = let (t, r) = goTok (Just q) xs in (x:t, r)
        | otherwise = let (t, r) = goTok (Just q) cs in (c:t, r)
