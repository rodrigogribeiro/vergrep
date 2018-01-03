module PrefixAntimirov where

import qualified Prelude
import qualified Antimirov
import qualified Regex

antimirov_prefix :: Regex.Coq_regex -> Prelude.String -> Prelude.Bool
antimirov_prefix e s =
  case s of {
   [] -> Regex.null e;
   (:) a' s' ->
    (Prelude.||) (Regex.null e)
      (Prelude.any (\e' -> antimirov_prefix e' s') (Antimirov.pderiv a' e))}

