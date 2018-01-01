Set Implicit Arguments.

Require Import
        Syntax.Regex
        Derivatives.Brzozowski
        Prefix.PrefixDef
        Tactics.Tactics.


Fixpoint brzozowski_prefix (e : regex)(s : string) : bool :=
  match s with
  | EmptyString => null e
  | String a' s' =>
    orb (null e) (brzozowski_prefix (deriv a' e) s')
  end.


Theorem brzozowski_prefix_sound
  : forall s e, Is_true (brzozowski_prefix e s) -> prefix e s.
Proof.
  induction s ; intros e H ; simpl in *.
  +
    apply null_sound in H.
    apply MkPrefix with (x := "")(y := "") ; auto.
  +
    apply orb_prop_elim in H.
    destruct H.
    -
      apply null_sound in H.
      apply MkPrefix with (x := "")(y := String a s) ; auto.
    -
      apply IHs in H.
      inverts* H.
      apply deriv_sound in H0.
      apply MkPrefix with (x := String a x)(y := y) ; auto.        
Qed.

Theorem brzozowski_prefix_complete
  : forall s e, prefix e s -> Is_true (brzozowski_prefix e s).
Proof.
  induction s ; intros e H ; simpl in * ; inverts* H.
  +
    apply empty_string_concat in H1 ; destruct H1 ; substs.
    apply null_complete in H0 ; auto.
  +
    destruct x ; simpl in *.
    -
      substs.
      apply null_complete in H0.
      apply orb_prop_intro.
      left*.
    -
      injects H1.
      apply deriv_complete in H0.
      apply orb_prop_intro ; right*.
Qed.