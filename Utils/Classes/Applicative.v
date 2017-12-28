Set Implicit Arguments.

Require Import
        Utils.Functions.Functions
        Utils.Classes.Functor.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (f : Type -> Type) := {
  is_functor :> Functor f ; 
  pure : forall a : Type, a -> f a;
  ap   : forall a b : Type, f (a -> b) -> f a -> f b
    where "f <*> g" := (ap f g)
 }.


Notation "pure[ M ]" := (@pure M _ _) (at level 19, M at next level).
Notation "pure[ M N ]" := (@pure (fun X => M (N X)) _ _) (at level 9).

Notation "ap[ M ]" := (@ap M _ _ _) (at level 9).
Notation "ap[ M N ]" := (@ap (fun X => M (N X)) _ _ _) (at level 9).
Notation "ap[ M N O ]" := (@ap (fun X => M (N (O X))) _ _ _) (at level 9).

Infix "<*>" := ap (at level 28, left associativity).
Notation "x <**> f" := (ap f x) (at level 28, left associativity).
Notation "x <**[ M ]> f" := (@ap M _ _ _ f x) (at level 28, left associativity).
Infix "<*[ M ]>" :=
  (@ap M _ _ _) (at level 28, left associativity, only parsing).

Definition liftA2 {m : Type -> Type}`{M : Applicative m} {A B C : Type}
  (f : A -> B -> C) (x : m A) (y : m B) : m C := @ap m M _ _ (fmap f x) y.

Infix "*>" := (liftA2 (const id)) (at level 28, left associativity).
Infix "<*" := (liftA2 const) (at level 28, left associativity).
