Set Implicit Arguments.

Require Import
        String
        Syntax.Regex
        Substring.SubstringDef
        Prefix.PrefixDef
        Prefix.PrefixAntimirov
        Derivatives.Antimirov
        Tactics.Tactics.


Fixpoint antimirov_substring (e : regex)(s : string) : bool :=
  match s with
  | EmptyString => null e
  | String a' s' =>
    orb (antimirov_prefix e (String a' s'))
        (antimirov_substring e s')
  end.


Theorem antimirov_substring_sound
  : forall s e, Is_true (antimirov_substring e s) -> substring e s.
Proof.
  induction s ; intros e H ; simpl in *.
  +
    apply null_sound in H.
    eapply MkSubstring with (xs := "")(ys := "")(zs := "") ; auto.
  +
    apply orb_prop_elim in H.
    destruct H.
    -
      apply orb_prop_elim in H.
      destruct H.
      *
        apply null_sound in H.
        eapply MkSubstring with (xs := "")(ys := "")(zs := String a s) ; auto.
      *
        apply Is_true_eq_true in H.
        apply existsb_exists in H.
        destruct H as [e' [Hin Heq]].
        apply Is_true_eq_left in Heq.
        apply antimirov_prefix_sound in Heq.
        inverts Heq.
        assert (Hx : x <<<- (pderiv a e)).
           unfolds.
           apply Exists_exists ; eexists ; eauto.
        eapply pderiv_sound in Hx ; eauto.
        apply MkSubstring with (xs := "")(ys := String a x)(zs := y) ; auto.
    -    
      apply IHs in H.
      inverts* H.
      apply MkSubstring with (xs := String a xs)
                             (ys := ys)
                             (zs := zs) ; auto.
Qed.

Theorem antimirov_substring_complete
  : forall s e, substring e s -> Is_true (antimirov_substring e s).
Proof.
  induction s ; intros e H ; inverts* H.
  +
    apply empty_string_concat in H1.
    destruct H1.
    symmetry in H1.
    apply empty_string_concat in H1.
    destruct H1.
    substs.
    apply null_complete ; auto.
  +
    destruct xs.
    -
      destruct ys.
      *
        simpl in H1.
        substs.
        simpl.
        apply orb_prop_intro ; left.
        apply orb_prop_intro ; left.
        apply null_complete ; auto.
      *
        simpl in *.
        injects H1.
        eapply pderiv_complete in H0 ; eauto.
        apply orb_prop_intro ; left*.
        apply orb_prop_intro ; right*.
        apply Is_true_eq_left.
        apply existsb_exists.
        inverts H0.
        **
          exists x ; simpl ; splits*.
          apply Is_true_eq_true.
          apply antimirov_prefix_complete.
          eapply MkPrefix ; eauto.
        **
          apply Exists_exists in H1.
          destruct H1 as [e' [Hin Heq]].
          exists e' ; simpl ; splits*.
          apply Is_true_eq_true.
          apply antimirov_prefix_complete.
          eapply MkPrefix ; eauto.
    -
      injects H1.
      simpl.
      apply orb_prop_intro ; right.
      apply IHs.
      eapply MkSubstring ; eauto.
Qed.