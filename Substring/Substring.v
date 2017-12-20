Set Implicit Arguments.

Require Import
        Syntax.Regex
        Prefix.Prefix
        Tactics.Tactics.

Inductive substring : regex -> string -> Prop :=
|  MkSubstring : forall e xs ys zs s, ys <<- e ->
                               s = xs ++ ys ++ zs ->
                               substring e s.

Hint Constructors substring.

Lemma not_empty_substring
  : forall e, ~ prefix e "" -> ~ substring e "".
Proof.
  intros e H ; intro contra ; inverts* contra.
  apply empty_string_concat in H1. destruct H1 ; substs.
  simpl in *. symmetry in H2. apply empty_string_concat in H2. destruct H2. substs.
  assert (prefix e "") by (econstructor ; eauto ; reflexivity). contradiction.
Qed.

Lemma not_cons_substring
  : forall e x xs, ~ prefix e (String x xs) ->
              ~ substring e xs ->
              ~ substring e (String x xs).
Proof.
  intros e x xs Hp Hsxs ; intro contra ; inverts* contra.
  destruct xs0 ; simpl in *.
  assert (prefix e (String x xs))
    by (econstructor ; eauto ; reflexivity). contradiction.
  injects H0.
  assert (substring e (xs0 ++ ys ++ zs)).
  eapply MkSubstring with (xs := xs0)
                          (ys := ys)
                          (zs := zs) ; eauto.
  contradiction.
Qed.

Lemma prefix_is_substring
  : forall e s, prefix e s -> substring e s.
Proof.
  intros e s H ; inverts* H.
  apply MkSubstring with (xs := "")(ys := x)(zs := y) ; auto.
Qed.
Hint Resolve not_empty_substring not_cons_substring.