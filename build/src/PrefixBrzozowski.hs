module PrefixBrzozowski where

import qualified Prelude
import qualified Brzozowski
import qualified Regex

brzozowski_prefix :: Regex.Coq_regex -> Prelude.String -> Prelude.Bool
brzozowski_prefix e s =
  case s of {
   [] -> Regex.null e;
   (:) a' s' ->
    (Prelude.||) (Regex.null e)
      (brzozowski_prefix (Brzozowski.deriv a' e) s')}

