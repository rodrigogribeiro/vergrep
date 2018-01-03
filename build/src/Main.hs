module Main where

import Argument 
import RegexParser
import Regex
import Data.Maybe
import SubstringAntimirov
import SubstringBrzozowski
import System.Environment (getArgs)

versionInfo :: String
versionInfo = "vergrep - version 0.1"

usageInfo :: String
usageInfo =  "Usage: vergrep [OPTIONS] [REGEXP] [FILELIST]" ++
          "\n\nwhere\nOPTIONS\n-B: parse with Brzozowski derivatives\n" ++
          "-A: parse with Antimirov derivatives\n" ++
          "-v: Show version information" ++
          "-h: help message"

exec :: Algorithm -> Coq_regex -> String -> IO ()
exec Antimirov e s
   | antimirov_substring e s = putStrLn s
   | otherwise = return ()
exec Brzozowski e s
   | brzozowski_substring e s = putStrLn s
   | otherwise = return ()

run :: Algorithm -> [String] -> Coq_regex -> IO ()
run alg xs e = mapM_ step xs
               where
                 step f = readFile f >>= mapM_ (exec alg e) . lines 

parseRegexAndRun :: Options -> IO ()
parseRegexAndRun opt
  | isNothing (Argument.regex opt)
     = putStrLn usageInfo
  | otherwise
     = do
         let r = parseRegex (fromJust (Argument.regex opt))
         either (const (putStrLn usageInfo))
                (run (alg opt) (files opt)) r

main :: IO ()
main
  = do
      args <- getArgs
      let opt = parseOptions args
      if version opt then putStrLn versionInfo
        else if help opt then putStrLn usageInfo
              else parseRegexAndRun opt
