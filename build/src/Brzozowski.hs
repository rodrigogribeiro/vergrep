module Brzozowski where

import qualified Prelude
import qualified Ascii
import qualified Regex
import qualified Smart

deriv :: Ascii.Coq_ascii -> Regex.Coq_regex -> Regex.Coq_regex
deriv a e =
  case e of {
   Regex.Chr c ->
    case Ascii.ascii_dec a c of {
     Prelude.True -> Regex.Eps;
     Prelude.False -> Regex.Emp};
   Regex.Cat e1 e2 ->
    case Regex.null e1 of {
     Prelude.True ->
      Smart.choice_smart (Smart.cat_smart (deriv a e1) e2) (deriv a e2);
     Prelude.False -> Smart.cat_smart (deriv a e1) e2};
   Regex.Choice e1 e2 -> Smart.choice_smart (deriv a e1) (deriv a e2);
   Regex.Star e1 -> Smart.cat_smart (deriv a e1) (Smart.star_smart e1);
   _ -> Regex.Emp}

