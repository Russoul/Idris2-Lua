module Main

import Data.Maybe
import Data.List
import Data.List1
import Data.String

import System
import System.Directory
import System.File
import System.Info
import System.Path

%default covering

------------------------------------------------------------------------
-- Test cases

chezTests : List String
chezTests
   = ["chez001", "chez002", "chez003", {-"chez004" (Bits),-} "chez005", "chez006",
      "chez007", "chez008", "chez009", {- "chez010" (C callback),-} "chez011", "chez012",
      {-"chez013" (FFI Field),-} {-"chez014" (FFI Network),-} {- "chez015" (Int overflow) -} "chez016", "chez017", "chez018",
      "chez019", "chez020",{- "chez021", "chez022", "chez023", "chez024", -}
      "chez025", "chez026", "chez027",
      "reg001"]

luaTests : List String
luaTests = ["lua001", "lua002", "lua003", "lua004", "lua005"]

------------------------------------------------------------------------
-- Options

||| Options for the test driver.
record Options where
  constructor MkOptions
  ||| Name of the idris2 executable
  idris2      : String
  ||| Name of the codegenerator to use for `exec`
  codegen     : Maybe String
  ||| Should we only run some specific cases?
  onlyNames   : List String
  ||| Should we run the test suite interactively?
  interactive : Bool

usage : String
usage = "Usage: runtests <idris2 path> [--interactive]"

options : List String -> Maybe Options
options args = case args of
    (_ :: idris2 :: rest) => go rest (MkOptions idris2 Nothing [] False)
    _ => Nothing

  where

    go : List String -> Options -> Maybe Options
    go rest opts = case rest of
      []                      => pure opts
      ("--interactive" :: xs) => go xs (record { interactive = True } opts)
      ("--cg" :: cg :: xs)    => go xs (record { codegen = Just cg } opts)
      ("--only" :: xs)        => pure $ record { onlyNames = xs } opts
      _ => Nothing

------------------------------------------------------------------------
-- Actual test runner

fail : String -> IO ()
fail err
    = do putStrLn err
         exitWith (ExitFailure 1)

-- on Windows, we just ignore backslashes and slashes when comparing,
-- similarity up to that is good enough. Leave errors that depend
-- on the confusion of slashes and backslashes to unix machines.
normalize : String -> String
normalize str =
    if isWindows
      then pack $ filter (\ch => ch /= '/' && ch /= '\\') (unpack str)
      else str

runTest : Options -> String -> IO Bool
runTest opts testPath
    = do ignore $ changeDir testPath
         isSuccess <- runTest'
         ignore $ changeDir "../.."
         pure isSuccess
    where
        getAnswer : IO Bool
        getAnswer = do
          str <- getLine
          case str of
            "y" => pure True
            "n" => pure False
            _   => do putStrLn "Invalid Answer."
                      getAnswer

        printExpectedVsOutput : String -> String -> IO ()
        printExpectedVsOutput exp out = do
          putStrLn "Expected:"
          printLn exp
          putStrLn "Given:"
          printLn out

        mayOverwrite : Maybe String -> String -> IO ()
        mayOverwrite mexp out = do
          the (IO ()) $ case mexp of
            Nothing => putStr $ unlines
              [ "Golden value missing. I computed the following result:"
              , out
              , "Accept new golden value? [yn]"
              ]
            Just exp => do
              putStrLn "Golden value differs from actual value."
              code <- system "git diff --no-index --exit-code --word-diff=color expected output"
              when (code < 0) $ printExpectedVsOutput exp out
              putStrLn "Accept actual value as new golden value? [yn]"
          b <- getAnswer
          when b $ do Right _ <- writeFile "expected" out
                          | Left err => print err
                      pure ()
        runTest' : IO Bool
        runTest'
            = do putStr $ testPath ++ ": "
                 ignore $ system $ "sh ./run " ++ idris2 opts ++ " | tr -d '\\r' > output"
                 Right out <- readFile "output"
                     | Left err => do print err
                                      pure False
                 Right exp <- readFile "expected"
                     | Left FileNotFound => do
                         if interactive opts
                           then mayOverwrite Nothing out
                           else print FileNotFound
                         pure False
                     | Left err => do print err
                                      pure False
                 let result = normalize out == normalize exp
                 -- The issue #116 that made this necessary is fixed, but
                 -- please resist putting 'result' here until it's also
                 -- fixed in Idris2-boot!
                 if normalize out == normalize exp
                    then putStrLn "success"
                    else do
                      putStrLn "FAILURE"
                      if interactive opts
                         then mayOverwrite (Just exp) out
                         else printExpectedVsOutput exp out

                 pure result

exists : String -> IO Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

pathLookup : List String -> IO (Maybe String)
pathLookup names = do
  path <- getEnv "PATH"
  let pathList = List1.forget $ split (== pathSeparator) $ fromMaybe "/usr/bin:/usr/local/bin" path
  let candidates = [p ++ "/" ++ x | p <- pathList,
                                    x <- names]
  firstExists candidates

findLua : IO (Maybe String)
findLua
    = do Just lua <- getEnv "LuaExe" | Nothing => pathLookup ["lua"]
         pure $ Just lua

runLuaTests : Options -> List String -> IO (List Bool)
runLuaTests opts tests
    = do chexec <- findLua
         maybe (do putStrLn "Lua not found"
                   pure [])
               (\c => do putStrLn $ "Found Lua at " ++ c
                         traverse (runTest opts) tests)
               chexec

filterTests : Options -> List String -> List String
filterTests opts = case onlyNames opts of
  [] => id
  xs => filter (\ name => any (`isInfixOf` name) xs)

main : IO ()
main
    = do args <- getArgs
         let (Just opts) = options args
              | _ => do print args
                        putStrLn usage

         let filteredNonCGTests =
              filterTests opts $ concat $ the (List _) [
                   testPaths "chez" chezTests
                 , testPaths "lua" luaTests
                 ]

         res <- runLuaTests opts $ filteredNonCGTests

         putStrLn (show (length (filter id res)) ++ "/" ++ show (length res)
                       ++ " tests successful")
         if (any not res)
            then exitWith (ExitFailure 1)
            else exitWith ExitSuccess
    where
         testPaths : String -> List String -> List String
         testPaths dir tests = map (\test => dir ++ "/" ++ test) tests
