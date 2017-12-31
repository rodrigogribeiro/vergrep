module Smart where

import qualified Prelude
import qualified Regex

choice_smart :: Regex.Coq_regex -> Regex.Coq_regex -> Regex.Coq_regex
choice_smart e e' =
  case e of {
   Regex.Emp -> e';
   _ -> case e' of {
         Regex.Emp -> e;
         _ -> Regex.Choice e e'}}

cat_smart :: Regex.Coq_regex -> Regex.Coq_regex -> Regex.Coq_regex
cat_smart e e' =
  case e of {
   Regex.Emp -> Regex.Emp;
   Regex.Eps -> e';
   _ ->
    case e' of {
     Regex.Emp -> Regex.Emp;
     Regex.Eps -> e;
     _ -> Regex.Cat e e'}}

star_smart :: Regex.Coq_regex -> Regex.Coq_regex
star_smart e =
  case e of {
   Regex.Emp -> Regex.Eps;
   Regex.Eps -> Regex.Eps;
   _ -> Regex.Star e}

