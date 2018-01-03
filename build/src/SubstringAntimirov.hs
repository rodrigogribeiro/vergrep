module SubstringAntimirov where

import qualified Prelude
import qualified PrefixAntimirov
import qualified Regex

antimirov_substring :: Regex.Coq_regex -> Prelude.String -> Prelude.Bool
antimirov_substring e s =
  case s of {
   [] -> Regex.null e;
   (:) a' s' ->
    (Prelude.||) (PrefixAntimirov.antimirov_prefix e ((:) a' s'))
      (antimirov_substring e s')}

