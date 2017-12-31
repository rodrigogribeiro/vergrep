module SubstringAntimirov where

import qualified Prelude
import qualified PrefixAntimirov
import qualified Regex

antimirov_substring :: Regex.Coq_regex -> Prelude.String -> Prelude.Bool
antimirov_substring e s =
  case s of {
   [] -> Regex.null e;
   (:) a' s' ->
    case PrefixAntimirov.antimirov_prefix e ((:) a' s') of {
     Prelude.True -> Prelude.True;
     Prelude.False -> antimirov_substring e s'}}

