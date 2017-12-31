Set Implicit Arguments.

Require Import
        List
        String
        Syntax.Regex
        Derivatives.Antimirov
        Prefix.PrefixDef
        Tactics.Tactics.


Lemma exists_prefix
  : forall E ys zs, Exists (fun e => ys <<- e) E -> Exists (fun e => prefix e (ys ++ zs)) E.
Proof.
  induction E ; intros ys zs H ; inverts* H.
Qed.

Lemma in_prefix
  : forall ys zs E, ys <<<- E -> Exists (fun e => prefix e (ys ++ zs)) E.
Proof.
  intros ys zs E H. unfolds in H.
  apply exists_prefix ; eauto.
Qed.

Hint Resolve in_prefix.


Fixpoint antimirov_prefix (e : regex)(s : string) : bool :=
  match s with
  | EmptyString => null e
  | String a' s' =>
    orb (null e)
        (existsb (fun e' => antimirov_prefix e' s') (pderiv a' e))
  end.

Theorem antimirov_prefix_sound
  : forall s e, Is_true (antimirov_prefix e s) -> prefix e s.
Proof.
  induction s ; intros e ; simpl in * ; intros H.
  +
    apply null_sound in H.
    apply MkPrefix with (x := "")(y := "") ; simpl in * ; auto.
  +
    apply orb_prop_elim in H.
    destruct H.
    -
      apply null_sound in H.
      apply MkPrefix with (x := "")(y := String a s) ; auto.
    -
      apply Is_true_eq_true in H.
      apply existsb_exists in H.
      destruct H as [e' [Hin Heq]].
      apply Is_true_eq_left in Heq.
      apply IHs in Heq.
      inverts* Heq.
      assert (Hx : x <<<- pderiv a e).
      *
        unfolds.
        apply Exists_exists.
        exists e' ; auto.
      *
        apply (pderiv_sound e a (eq_refl (pderiv a e))) in Hx.
        apply MkPrefix with (x := String a x)(y := y) ; simpl ; eauto.
Qed.

Theorem antimirov_prefix_complete
  : forall s e, prefix e s -> Is_true (antimirov_prefix e s).
Proof.
  induction s ; intros e ; simpl in * ; intros H.
  +
    inverts* H.
    apply empty_string_concat in H1.
    destruct H1.
    substs.
    apply null_complete in H0 ; auto.
  +
    inverts* H.
    destruct x.
    simpl in *.
    substs.
    apply null_complete in H0.
    apply orb_prop_intro ; left*.
    injects* H1.
    eapply pderiv_complete in H0 ; eauto.
    unfolds in H0.
    apply Exists_exists in H0.
    destruct H0 as [e'[HIn Hs]].
    assert (Hx : prefix e' (x ++ y)).
    -
      econstructor ; eauto.
    -
      apply IHs in Hx.
      apply orb_prop_intro ; right.
      apply Is_true_eq_left.
      apply existsb_exists.
      apply Is_true_eq_true in Hx.
      exists e' ; splits ; auto.
Qed.