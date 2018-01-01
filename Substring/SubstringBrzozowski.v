Set Implicit Arguments.

Require Import
        Syntax.Regex
        Derivatives.Brzozowski
        Prefix.PrefixDef
        Prefix.PrefixBrzozowski
        Substring.SubstringDef
        Tactics.Tactics.

Fixpoint brzozowski_substring (e : regex)(s : string) : bool :=
  match s with
  | EmptyString => null e
  | String a' s' =>
    orb (brzozowski_prefix e (String a' s'))
        (brzozowski_substring e s')
  end.

Theorem brzozowski_substring_sound
  : forall s e, Is_true (brzozowski_substring e s) -> substring e s.
Proof.
  induction s ; intros e H ; simpl in *.
  +
    apply null_sound in H.
    apply MkSubstring with (xs := "")(ys := "")(zs := "") ; eauto.
  + 
    apply orb_prop_elim in H.
    destruct H.
    -
      apply orb_prop_elim in H.
      destruct H.
      *
        apply null_sound in H.
        apply MkSubstring with (xs := "")(ys := "") (zs := String a s) ; eauto.
      *
        apply brzozowski_prefix_sound in H.
        inverts* H.
        apply deriv_sound in H0.
        apply MkSubstring with (xs := "")(ys := String a x)(zs := y) ; eauto.
    -
      apply IHs in H.
      inverts H.
      apply MkSubstring with (xs := String a xs)
                             (ys := ys)
                             (zs := zs) ; auto.
Qed.

Theorem brzozowski_substring_complete
  : forall s e, substring e s -> Is_true (brzozowski_substring e s).
Proof.
  induction s ; intros e H ; inverts* H.
  +
    apply empty_string_concat in H1.
    destruct H1.
    symmetry in H1.
    apply empty_string_concat in H1.
    destruct H1.
    substs.
    simpl.
    apply null_complete ; auto.
  +
    destruct xs ; simpl in *.
    -
      destruct ys ; simpl in *.
      *
        substs.
        apply orb_prop_intro ; left ; apply orb_prop_intro ; left ;
          apply null_complete in H0 ; auto.
      * 
        injects H1.
        apply orb_prop_intro.
        left.
        apply orb_prop_intro ; right.
        apply brzozowski_prefix_complete.
        apply deriv_complete in H0.
        apply MkPrefix with (x := ys)(y := zs) ; auto.
    -
      injects H1.
      apply orb_prop_intro ; right.
      apply IHs.
      apply MkSubstring with (xs := xs)(ys := ys)(zs := zs) ; auto.
Qed.