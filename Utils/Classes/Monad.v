Set Implicit Arguments.

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

