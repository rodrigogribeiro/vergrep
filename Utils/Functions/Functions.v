Set Implicit Arguments.

(** some default polymorphic functions *)

Section FUNCTIONS.
  Variables A B C : Type.

  Definition id (x : A) := x.

  Definition const (x : A)(y : B) := x.
  
  Definition uncurry (f : A -> B -> C)(p : A * B) :=
    match p with
    | (x,y) => f x y
    end.

  Definition curry (f : (A * B) -> C)(x : A)(y : B) : C :=
    f (x , y).

  Definition compose (f : B -> C)(g : A -> B)(x : A) : C :=
    f (g x).

  Definition flip (f : B -> A -> C)(x : A)(y : B) := f y x.
End FUNCTIONS.

Notation "f ':@:' g" := (compose f g)(at level 40, left associativity).

(* useful function on sumbool *)

Definition sumbool_to_bool {A B : Prop} (p : {A} + {B}) :=
  if p then true else false.