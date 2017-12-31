module Regex where

import qualified Prelude
import qualified Ascii

data Coq_regex =
   Emp
 | Eps
 | Chr Ascii.Coq_ascii
 | Cat Coq_regex Coq_regex
 | Choice Coq_regex Coq_regex
 | Star Coq_regex

null :: Coq_regex -> Prelude.Bool
null e =
  case e of {
   Emp -> Prelude.False;
   Chr _ -> Prelude.False;
   Cat e1 e2 ->
    case null e1 of {
     Prelude.True -> null e2;
     Prelude.False -> Prelude.False};
   Choice e1 e2 ->
    case null e1 of {
     Prelude.True -> Prelude.True;
     Prelude.False -> null e2};
   _ -> Prelude.True}

