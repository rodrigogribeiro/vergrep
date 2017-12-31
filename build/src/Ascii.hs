module Ascii where

import qualified Prelude
import qualified Bool
import qualified Specif

data Coq_ascii =
   Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool Prelude.Bool Prelude.Bool

ascii_rect :: (Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool
              -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool
              -> a1) -> Coq_ascii -> a1
ascii_rect f a =
  case a of {
   Ascii x x0 x1 x2 x3 x4 x5 x6 -> f x x0 x1 x2 x3 x4 x5 x6}

ascii_rec :: (Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
             Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
             a1) -> Coq_ascii -> a1
ascii_rec =
  ascii_rect

ascii_dec :: Coq_ascii -> Coq_ascii -> Prelude.Bool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x ->
    case x of {
     Ascii b8 b9 b10 b11 b12 b13 b14 b15 ->
      Specif.sumbool_rec (\_ ->
        Specif.sumbool_rec (\_ ->
          Specif.sumbool_rec (\_ ->
            Specif.sumbool_rec (\_ ->
              Specif.sumbool_rec (\_ ->
                Specif.sumbool_rec (\_ ->
                  Specif.sumbool_rec (\_ ->
                    Specif.sumbool_rec (\_ -> Prelude.True) (\_ ->
                      Prelude.False) (Bool.bool_dec b7 b15)) (\_ ->
                    Prelude.False) (Bool.bool_dec b6 b14)) (\_ ->
                  Prelude.False) (Bool.bool_dec b5 b13)) (\_ ->
                Prelude.False) (Bool.bool_dec b4 b12)) (\_ -> Prelude.False)
              (Bool.bool_dec b3 b11)) (\_ -> Prelude.False)
            (Bool.bool_dec b2 b10)) (\_ -> Prelude.False)
          (Bool.bool_dec b1 b9)) (\_ -> Prelude.False) (Bool.bool_dec b0 b8)})
    a b

