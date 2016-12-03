(** Antimirov partial derivatives and its properties *)

Set Implicit Arguments.

Require Import
        Syntax.Regex
        Tactics.LibTactics
        List
        ListSet.

Section LISTSET.

  Definition empty := empty_set regex.

  Definition singleton e := set_add regex_eq_dec e empty.

  Definition union := set_union regex_eq_dec.

  Lemma union_nil_l
    : forall x l
    , In x (union nil l) <-> In x l.
  Proof.
    intros x l ; splits ; intro H.
    +
      induction l ; simpl in *.
      -
        contradiction.
      -
        destruct (regex_eq_dec a x).
        *
          left*.
        *
          right*.
          apply IHl.
          eapply set_add_elim2 ; eauto.
    +
      apply set_union_intro2 ; auto.
  Qed.
  
  Lemma set_exists__union
    : forall l l' P
    , Exists P (union l l') <->
      Exists P l \/ Exists P l'.
  Proof.
    intros l l' P ; split ; intros H.
    +
      apply Exists_exists in H.
      destruct H as [x [HIx HPx]].
      unfold union in *.
      apply set_union_elim in HIx.
      destruct* HIx.
      -
        destruct l ; simpl in * ; try contradiction.
        destruct H ; substs ; left*.
        apply Exists_cons_tl ; auto.
        assert (Ha : exists x, set_In x l /\ P x).
          eexists ; splits*.
        apply Exists_exists in Ha ; auto.
      -
        destruct l' ; simpl in * ; try contradiction.
        destruct H ; substs ; right*.
        assert (Ha : exists x, set_In x l' /\ P x).
          eexists ; splits*.
        apply Exists_exists in Ha ; auto.
    +
      inverts H.
      -
        apply Exists_exists in H0.
        destruct H0 as [x [HIx HPx]].
        apply Exists_exists ; eexists ; splits ; eauto.
        apply set_union_intro1 ; auto.
      -
        apply Exists_exists in H0.
        destruct H0 as [x [HIx HPx]].
        apply Exists_exists ; eexists ; splits ; eauto.
        apply set_union_intro2 ; auto.
  Qed.

  Lemma set_exists_map
    : forall l P (f : regex -> regex)
    , Exists P (map f l) ->
      Exists (fun e => P (f e)) l.
  Proof.
    induction l ; intros P f H ; simpl in * ; inverts* H.
  Qed.
End LISTSET.  

Fixpoint pderiv (a : ascii)(e : regex) : list regex :=
  match e with
  | #0 => empty
  | #1 => empty
  | $ a' =>
    match ascii_dec a a' with
    | left _ => singleton #1
    | right _ => empty                      
    end
  | (e1 @ e2) =>
    match null e1 with
    | left _ =>
      union (pderiv a e2)
            (map (fun e' => e' @ e2)
                 (pderiv a e1))
    | right _ =>
      map (fun e' => e' @ e2) (pderiv a e1)
    end
  | (e1 :+: e2) =>
      union (pderiv a e1) (pderiv a e2)
  | (e1 ^*) =>
     map (fun e' => e' @ (e1 ^*)) (pderiv a e1)
end.

Definition in_regex_set s es :=
  Exists (fun e' => s <<- e') es. 

Notation "s '<<<-' e" := (in_regex_set s e)(at level 40).

Theorem pderiv_sound
  :  forall e a s
  ,  s <<<- (pderiv a e)
     -> (String a s) <<- e.
Proof.
  induction e ; intros a' s H ;
    unfolds in_regex_set ; simpl in * ;
      repeat (match goal with
              | [H : Exists _ empty |- _] =>
                inverts* H
              | [H : Exists _ (singleton _) |- _] =>
                inverts* H
              | [H : Exists _ nil |- _] =>
                inverts* H
              | [H : _ \/ _ |- _] =>
                inverts* H
              | [H : Exists _ (union _ _) |- _] =>
                apply set_exists__union in H
              | [H : Exists _ (map _ _) |- _] =>
                apply set_exists_map in H
              | [H : _ <<- #1 |- _] =>
                inverts* H
              | [H : context[if ?E then _ else _] |- _] =>
                  destruct* E
              end ; substs ; eauto).
  +
    apply Exists_exists in H0.
    destruct H0 as [x [HIx Hsx]].
    inverts* Hsx.
    rewrite str_append_rewind.
    clear i.
    econstructor ; eauto.
    apply IHe1.
    apply Exists_exists.
    eexists ; eauto.
  +
    apply Exists_exists in H.
    destruct H as [x [HIx Hsx]].
    inverts* Hsx.
    rewrite str_append_rewind.
    econstructor ; eauto.
    apply IHe1.
    apply Exists_exists.
    eexists ; eauto.
  +
    apply Exists_exists in H.
    destruct H as [x [HIx Hsx]].
    inverts* Hsx.
    rewrite str_append_rewind.
    apply InStarRight with (a := a')(s := s0)(s' := s') ; auto.
    apply IHe.
    apply Exists_exists.
    eexists ; eauto.
Qed.

Theorem pderiv_complete
  : forall e a s
  , (String a s) <<- e ->
    s <<<- (pderiv a e).
Proof.
  induction e ; intros a' s H ; simpl in * ; inverts* H ;
    unfold in_regex_set in * ;
    repeat (match goal with
            | [H : context[if ?E then _ else _] |- _] =>
              destruct* H
            | [ |- context[if ?E then _ else _]] =>
              destruct* E
            | [H : ?a <> ?a |- _] =>
              elim H ; auto
            end ; try solve [econstructor ; eauto]).
  +
    destruct s0 ; simpl in * ; substs.
    apply set_exists__union ; eauto.
    inverts* H5.
    apply set_exists__union.
    lets J : IHe1 H2.
    apply Exists_exists in J.
    destruct J as [x [HIx Hsx]].
    right.
    apply set_exists_map.
    rewrite map_map.
    apply Exists_exists.
    exists (x @ e2) ; split ; eauto.
    remember (pderiv a e1) as L.
    destruct L ; substs.
    inverts* HIx.
    simpl in *.
    inverts* HIx.
    right.
    apply in_map with (f := (fun x0 => x0 @ e2)) in H ; auto.
  +
    destruct s0 ; simpl in * ; substs ; try contradiction ; auto.
    inverts* H5.
    apply Exists_exists.
    lets J : IHe1 H2.
    apply Exists_exists in J.
    destruct J as [x [Hx Hsx]].
    exists (x @ e2) ; split ; eauto.
    apply in_map with (f := (fun e' => e' @ e2)) ; auto.
  +   
    apply set_exists__union ; eauto.
  +
    apply set_exists__union ; eauto.
  +
    inverts* H4.
    lets J : IHe H1.
    apply Exists_exists in J.
    destruct J as [x [Hx Hsx]].
    apply Exists_exists.
    exists (x @ (e ^*)) ; split ; eauto.
    apply in_map with (f := fun e' => e' @ (e ^*)) ; auto.
Qed.


Fixpoint antimirov' (s : string)(e : list regex) : list regex :=
  match s with
  | "" => e
  | String a s' =>
    antimirov' s' (flat_map (pderiv a) e)
  end.

Definition antimirov s e := antimirov' s (e :: nil).

Lemma antimirov'_sound
  : forall s e
  , "" <<<- (antimirov' s e)
    -> s <<<- e.
Proof.
  induction s ; intros e H ; simpl in * ; auto.
  +
    