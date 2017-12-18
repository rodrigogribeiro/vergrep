Set Implicit Arguments.

Require Import
        Syntax.Regex
        Tactics.LibTactics
        List
        String.

Import ListNotations.

Definition regexes := list regex.

Definition bigcat (s : regexes)(e : regex)
  := map (fun e' => e' @ e) s.

Fixpoint pderiv (a : ascii)(e : regex) : regexes :=
  match e with
  | #0 => []
  | #1 => [] 
  | $ a' =>
    match ascii_dec a a' with
    | left _ => [ #1 ]
    | right _ => []                      
    end
  | (e1 @ e2) =>
    match null e1 with
    | left _ =>
      (pderiv a e2) ++ (bigcat(pderiv a e1) e2)
    | right _ =>
      bigcat (pderiv a e1) e2
    end
  | (e1 :+: e2) =>
      (pderiv a e1) ++ (pderiv a e2)
  | (e1 ^*) =>
     bigcat (pderiv a e1) (e1 ^*)
  end.

Definition in_set (s : string)(es : regexes)
    := Exists (fun e => s <<- e) es.

Notation "s '<<<-' e" := (in_set s e)(at level 40).

Open Scope string_scope.

Lemma in_set_empty
  : forall s, ~ (s <<<- []).
Proof.
  intros s ; intro contra ; unfolds in contra ; inverts* contra.
Qed.

Lemma in_set_eps_singleton
  : forall s, s <<<- [ #1 ] -> s = "".
Proof.
  intros s H. inverts* H. inverts* H1. inverts* H1.
Qed.

Lemma in_append_left
  : forall E E' s, s <<<- E -> s <<<- (E ++ E')%list.
Proof.
  induction E ; intros E' s H.
  +
    apply in_set_empty in H ; elim H.
  +
    simpl.
    inverts* H.
    constructor ; auto.
    apply Exists_cons_tl ; auto.
    apply IHE ; auto.
Qed.

Lemma append_rewind {A : Type}
  : forall x (xs ys : list A), x :: (xs ++ ys)%list = ((x :: xs) ++ ys)%list.
Proof.
  intros ; auto.
Qed.


Lemma bigcat_cons
  : forall E e e' s, s <<<- (bigcat (e :: E) e') -> s <<- (e @ e') \/ s <<<- bigcat E e'.
Proof.
  induction E ; intros e e' s H ; simpl in * ; inverts* H.
Qed.

Lemma bigcat_in
  : forall E e' s, s <<<- bigcat E e' ->
              exists s1 s2 e, In e E /\ s1 <<- e /\ s2 <<- e' /\ s = s1 ++ s2.
Proof.
  induction E ; intros.
  +
    apply in_set_empty in H ; elim H.
  +
    apply bigcat_cons in H.
    destruct* H.
    inverts* H.
    exists s0 s' a ; splits* ; simpl ; left*.
    apply IHE in H.
    destruct* H as [s1 [s2 [e1 [Hin [Hs1 [Hs2 Heq]]]]]].
    exists s1 s2 e1 ; splits*.
    simpl. right*.
Qed.

Lemma in_append_right
  : forall E' E s, s <<<- E -> s <<<- (E' ++ E)%list.
Proof.
  induction E' ; intros ; simpl ; auto.
  +
    apply Exists_cons_tl ; apply IHE' ; auto.
Qed.

Lemma in_append :
  forall E E' s, s <<<- (E ++ E')%list <-> s <<<- E \/ s <<<- E'.
Proof.
  induction E ; intros ; split ; intros ; simpl in * ; eauto.
  +
    destruct H ; auto.
    apply in_set_empty in H ; contradiction.
  +
    inverts* H.
    -
      left ; constructor ; auto.
    -
      apply IHE in H1.
      destruct H1. 
      left ; apply Exists_cons_tl ; auto.
      right*.
  +
    destruct H as [H1 | H2].
    -
      rewrite append_rewind ; eapply in_append_left ; auto.
    -
      apply in_append_right with (E' := a :: E) in H2.
      simpl in * ; auto.
Qed.

Lemma str_append_rewind
  : forall s s' a, String a (s ++ s') = (String a s) ++ s'.
Proof.
  intros ; auto.
Qed.

Lemma in_set_cons
  : forall E e s, In e E -> s <<- e -> s <<<- E.
Proof.
  induction E ; intros ; simpl in * ; try contradiction.
  +
    destruct H ; substs.
    apply Exists_cons_hd ; auto.
    apply Exists_cons_tl. eapply IHE ; eauto.
Qed.

Theorem pderiv_sound
  :  forall e a s es 
  ,  es = pderiv a e ->
     s <<<- es
     -> (String a s) <<- e.
Proof.
  induction e ;  intros a' s es Heq Hin ; substs ; simpl in * ;
    repeat (match goal with
            | [H : _ <<<- [] |- _] => apply in_set_empty in H ; elim H
            | [H : context[if ?E then _ else _] |- _] =>
              destruct* E ; substs
            | [H : _ <<<- [#1] |- _] => apply in_set_eps_singleton in H ; substs
            end ; eauto).
  +
    apply in_append in Hin.
    destruct* Hin.
    apply bigcat_in in H.
    destruct* H as [s1 [s2 [e' [Hin [Hs1 [Hs2 Heq]]]]]].
    assert (Hex : s1 <<<- pderiv a' e1) by
        (eapply in_set_cons ; eauto).
    lets J : IHe1 Hex ; eauto.
    econstructor ; eauto.
    rewrite Heq ; auto.
  +
    apply bigcat_in in Hin.
    destruct Hin as [s1 [s2 [x [Hex [Hsx [Hs2 Heq]]]]]].
    assert (Hex1 : s1 <<<- pderiv a' e1) by
        (eapply in_set_cons ; eauto).
    lets J : IHe1 Hex1 ; eauto.
    econstructor ; eauto.
    rewrite Heq ; auto.
  +
    apply in_append in Hin.
    destruct* Hin.
  +
    apply bigcat_in in Hin.
    destruct Hin as [s1 [s2 [x [Hex [Hsx [Hs2 Heq]]]]]].
    assert (Hex1 : s1 <<<- pderiv a' e) by
        (eapply in_set_cons ; eauto).
    lets J : IHe Hex1 ; eauto.
    rewrite Heq.
    rewrite str_append_rewind.
    econstructor ; eauto.
Qed.


Lemma in_bigcat
   : forall E s s' e, s <<<- E -> s' <<- e -> (s ++ s') <<<- bigcat E e.
Proof.
  induction E ; intros.
  +
    apply in_set_empty in H ; elim H.
  +
    simpl.
    inverts* H.
    apply Exists_cons_hd ; eauto.
    lets J : IHE H2 H0.
    apply Exists_cons_tl ; eauto.
Qed.

Theorem pderiv_complete
  : forall e s',
  s' <<- e ->
  forall s a,  s' = (String a s) ->
    s <<<- (pderiv a e).
Proof.
  induction e ; intros s' H s a' Heq ; inverts* H ; try congruence.
  +
    injects H0 ; simpl ; eauto.
    destruct (ascii_dec a' a').
    unfolds ; apply Exists_cons_hd ; auto.
    contradiction.
  +
    destruct s0 ; simpl in * ; destruct (null e1) ; try contradiction.
    -
      substs.
      lets* J : IHe2 H4 s a' (eq_refl (String a' s)).
      eapply in_append_left ; eauto.
    -
      injects H0.
      lets* J : IHe1 H2 s0 a (eq_refl (String a s0)).
      eapply in_append_right ; eauto.
      eapply in_bigcat ; eauto.
    -
      injects H0.
      lets J : IHe1 H2 s0 a (eq_refl (String a s0)).
      eapply in_bigcat ; eauto.
  +
    lets* J : IHe1 H2 s a' Heq.
    simpl. eapply in_append_left ; eauto.
  +
    lets* J : IHe2 H2 s a' Heq.
    simpl ; eapply in_append_right ; eauto.
  +
    injects H0. simpl.
    lets J : IHe H1 s0 a (eq_refl (String a s0)).
    apply in_bigcat ; eauto.
Qed.