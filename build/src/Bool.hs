module Bool where

import qualified Prelude
import qualified Datatypes

bool_dec :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
bool_dec b1 b2 =
  Datatypes.bool_rec (\x ->
    case x of {
     Prelude.True -> Prelude.True;
     Prelude.False -> Prelude.False}) (\x ->
    case x of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}) b1 b2

