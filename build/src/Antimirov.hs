module Antimirov where

import qualified Prelude
import qualified Regex

type Coq_regexes = [] Regex.Coq_regex

bigcat :: Coq_regexes -> Regex.Coq_regex -> [] Regex.Coq_regex
bigcat s e =
  (Prelude.map) (\e' -> Regex.Cat e' e) s

pderiv :: Prelude.Char -> Regex.Coq_regex -> Coq_regexes
pderiv a e =
  case e of {
   Regex.Chr a' ->
    case (Prelude.==) a a' of {
     Prelude.True -> (:) Regex.Eps [];
     Prelude.False -> []};
   Regex.Cat e1 e2 ->
    case Regex.null e1 of {
     Prelude.True -> (Prelude.++) (pderiv a e2) (bigcat (pderiv a e1) e2);
     Prelude.False -> bigcat (pderiv a e1) e2};
   Regex.Choice e1 e2 -> (Prelude.++) (pderiv a e1) (pderiv a e2);
   Regex.Star e1 -> bigcat (pderiv a e1) (Regex.Star e1);
   _ -> []}

