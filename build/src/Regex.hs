module Regex where

import qualified Prelude

data Coq_regex =
   Emp
 | Eps
 | Chr Prelude.Char
 | Cat Coq_regex Coq_regex
 | Choice Coq_regex Coq_regex
 | Star Coq_regex

null :: Coq_regex -> Prelude.Bool
null e =
  case e of {
   Emp -> Prelude.False;
   Chr _ -> Prelude.False;
   Cat e1 e2 -> (Prelude.&&) (null e1) (null e2);
   Choice e1 e2 -> (Prelude.||) (null e1) (null e2);
   _ -> Prelude.True}

