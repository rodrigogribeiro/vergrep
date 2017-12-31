module SubstringBrzozowski where

import qualified Prelude
import qualified PrefixBrzozowski
import qualified Regex

brzozowski_substring :: Regex.Coq_regex -> Prelude.String -> Prelude.Bool
brzozowski_substring e s =
  case s of {
   [] -> Regex.null e;
   (:) a' s' ->
    case PrefixBrzozowski.brzozowski_prefix e ((:) a' s') of {
     Prelude.True -> Prelude.True;
     Prelude.False -> brzozowski_substring e s'}}

