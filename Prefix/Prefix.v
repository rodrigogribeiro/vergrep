Set Implicit Arguments.

Require Import
        Syntax.Regex
        Derivatives.Brzozowski.

(** definition of prefix that is matched by a re *)

Inductive prefix : regex -> string -> Prop :=
| MkPrefix
  : forall e s x y,
    x <<- e -> s = x ++ y -> prefix e s.

Hint Constructors prefix.

Lemma empty_not_prefix
  : forall e, ~ "" <<- e -> ~ prefix e "".
Proof.
  intros e H ; intro contra ; inverts* contra ;
    apply empty_string_concat in H1 ; destruct H1 ; substs ;
      contradiction.
Qed.

Lemma cons_not_prefix_brzozowski
  : forall e xs x, ~ "" <<- e -> ~ prefix (deriv x e) xs -> ~ prefix e (String x xs).
Proof.
  intros e xs x He Hpd ; intro Hxxs ; inverts* Hxxs.
  destruct x0 ; try contradiction ; simpl in *.
  injects H0.
  apply deriv_complete in H.
  assert (prefix (deriv a e) (x0 ++ y)) by
      (econstructor ; eauto).
  contradiction.
Qed.
