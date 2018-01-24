Require Import
        Ascii
        List 
        String
        Tactics.Tactics.

Import ListNotations.


Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String a' s' => a' :: string_to_list s'
  end.

Definition list_to_string (xs : list ascii) : string :=
  fold_right String EmptyString xs.


Lemma string_to_list_list_to_string
  : forall xs, string_to_list (list_to_string xs) = xs.
Proof.
  induction xs ; crush.
Qed.

Lemma list_to_string_string_to_list
  : forall s, list_to_string (string_to_list s) = s.
Proof.
  induction s ; crush.
Qed.
