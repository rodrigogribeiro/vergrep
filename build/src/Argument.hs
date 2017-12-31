module Argument where

import Data.Maybe

data Algorithm
  = Antimirov
  | Brzozowski
  deriving (Eq, Ord, Show)

data Options
  = Options {
      help :: Bool
    , version :: Bool
    , alg :: Algorithm
    , regex :: Maybe String
    , files :: [String]
    } 

defaultOptions :: Options
defaultOptions
  = Options False False Brzozowski Nothing [] 

parseOptions :: [String] -> Options
parseOptions
  = foldl step defaultOptions
    where
      step ac "-B" = ac{alg = Brzozowski}
      step ac "-A" = ac{alg = Antimirov}
      step ac "-v" = ac{version = True}
      step ac "-h" = ac{help = True}
      step ac s
         | isNothing (regex ac) = ac{regex = Just s}
         | otherwise = ac{files = s : (files ac)}
