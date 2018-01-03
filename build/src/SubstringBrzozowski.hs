module SubstringBrzozowski where

import qualified Prelude
import qualified PrefixBrzozowski
import qualified Regex

brzozowski_substring :: Regex.Coq_regex -> Prelude.String -> Prelude.Bool
brzozowski_substring e s =
  case s of {
   [] -> Regex.null e;
   (:) a' s' ->
    (Prelude.||) (PrefixBrzozowski.brzozowski_prefix e ((:) a' s'))
      (brzozowski_substring e s')}

