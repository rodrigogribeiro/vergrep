Set Implicit Arguments.

Require Import
        Utils.Functions.Functions.

Class Functor (f : Type -> Type) : Type := {
  fmap : forall {a b : Type}, (a -> b) -> f a -> f b
}.


Infix "<$>" := fmap (at level 28, left associativity, only parsing).
Infix "<$[ M ]>" :=
  (@fmap M _ _ _) (at level 28, left associativity, only parsing).
Notation "x <$ m" :=
  (fmap (const x) m) (at level 28, left associativity, only parsing).
Notation "x <&> f" :=
  (fmap f x) (at level 28, left associativity, only parsing).
