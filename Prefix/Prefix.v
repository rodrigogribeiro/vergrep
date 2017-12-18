Set Implicit Arguments.

Require Import
        Syntax.Regex.


(** definition of prefix that is matched by a re *)

Inductive Prefix : regex -> string -> Prop :=
| MkPrefix
  : forall e s x y,
    x <<- e -> s = x ++ y -> Prefix e s.

Hint Constructors Prefix.