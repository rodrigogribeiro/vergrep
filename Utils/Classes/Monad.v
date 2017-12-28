Set Implicit Arguments.

Require Import
        List
        Utils.Classes.Applicative.

Import ListNotations.

(* a simple monad definition and notations *)

Class Monad (M : Type -> Type) : Type :=
  {
    ret  : forall {A : Type}, A -> M A
  ; bind : forall {A B : Type}, M A -> (A -> M B) -> M B
  }.

Notation "a >>= f" := (bind a f) (at level 50, left associativity).

Definition wbind {M : Type -> Type}{A B : Type}`{Monad M}(ma : M A)(mb : M B) :=
  ma >>= (fun _ => mb).

Notation "a >> f" := (wbind _ a f) (at level 50, left associativity).
Notation "'do' a ← e ; c" := (e >>= (fun a => c a)) (at level 60, right associativity).

Section MONADICFUNCTIONS.
  Variable M : Type -> Type.
  Variables A B : Type.
  Context `{m : Monad M}.

  Fixpoint mapM (f : A -> M B)(xs : list A) : M (list B) :=
    match xs with
    | [] => ret []
    | (x :: xs) =>
      f x >>=
        (fun y => mapM f xs >>=
           (fun ys => ret (y :: ys)))
    end.

  Definition mapM_ (f : A -> M B)(xs : list A) : M unit :=
    (mapM f xs) >>= (fun _ => ret tt).
End MONADICFUNCTIONS.