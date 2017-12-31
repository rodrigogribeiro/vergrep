module List where

import qualified Prelude
import qualified Datatypes

map :: (a1 -> a2) -> ([] a1) -> [] a2
map f l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f a) (map f t)}

coq_Exists_dec :: ([] a1) -> (a1 -> Prelude.Bool) -> Prelude.Bool
coq_Exists_dec l pdec =
  Datatypes.list_rec Prelude.False (\a _ hrec ->
    case hrec of {
     Prelude.True -> Prelude.True;
     Prelude.False -> pdec a}) l

