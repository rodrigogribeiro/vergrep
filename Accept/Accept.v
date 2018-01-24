Set Implicit Arguments.

(** trying to reflect the RE membership
    relation *)

Require Import
        Syntax.Regex
        Utils.Functions.ListUtils.


Fixpoint accept (e : regex)(s : string) : bool :=
  match e with
  | #0 => false
  | #1 => if string_dec s "" then true else false
  | $ c => if string_dec s (String c EmptyString) then true else false
  | e1 :+: e2 => accept e1 s || accept e2 s
  | e1 @ e2 => forallb (fun p => accept e1 (fst p) && accept e2 (snd p)) (parts s)
  | _ => false
  end.
