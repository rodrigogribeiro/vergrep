Set Implicit Arguments.

Require Import
        Bool
        List
        Tactics.Tactics.

Import ListNotations.

Section SPLITS.
  Variable A : Type.

  Fixpoint splits (xs : list A) : list (list A * list A) :=
    match xs with
    | [] => [ ([],[]) ]
    | y :: ys =>
      ([], y :: ys) :: map (fun p => (y :: fst p, snd p)) (splits ys)
    end.

  Lemma splits_append_correct
    : forall xs ys zs, In (ys,zs) (splits xs) -> xs = ys ++ zs.
  Proof.
    induction xs ; crush.
    apply in_map_iff in H0.
    destruct H0 as [x [Heq Hin]].
    destruct x. inverts Heq.
    apply IHxs in Hin.
    rewrite Hin.
    auto.
  Qed.

  Lemma append_nil
    : forall (xs ys : list A), [] = xs ++ ys -> xs = [] /\ ys = [].
  Proof.
    induction xs ; destruct ys ; crush.
  Qed.

  Lemma append_splits_correct
    : forall xs ys zs, xs = ys ++ zs -> In (ys,zs) (splits xs).
  Proof.
    induction xs ; intros ; simpl in *.
    +
      apply append_nil in H ; destruct H ; substs*.
    +
      destruct ys. simpl in *. rewrite <- H. left*.
      right. simpl in *.
      apply in_map_iff.
      inverts* H.
      exists (ys,zs). simpl in *. splits*.
  Qed.

  Lemma splits_size
    : forall xs ys zs, In (ys,zs) (splits xs) -> length ys <= length xs /\
                                           length zs <= length xs.
  Proof.
    induction xs ; crush.
    apply in_map_iff in H0.
    destruct H0 as [x [Heq Hin]].
    inverts Heq. destruct x. simpl.
    lets J : IHxs Hin. destruct J ; crush.
    apply in_map_iff in H0.
    destruct H0 as [x [Heq Hin]].
    inverts Heq. destruct x. simpl.
    lets J : IHxs Hin. destruct J ; crush.
  Qed.
End SPLITS.

Section PARTS.
  Variable A : Type.

  Variable eqADec : forall (x y : A), {x = y} + {x <> y}.

  Definition athead (x : A)(xs : list (list A)) :=
    match xs with
    | [] => []
    | (y :: ys) => (x :: y) :: ys
    end.

  Definition non_empty (xs : list (list A)) :=
    match xs with
    | [] => false
    | _  => true
    end.

  Lemma non_empty_true
    : forall xs, non_empty xs = true -> exists y ys, xs = y :: ys.
  Proof.
    destruct xs ; intros ; crush.
    exists* l xs.
  Qed.

  Fixpoint parts (xs : list A) : list (list (list A)) :=
    match xs with
    | [] => [[]]
    | [ c ] => [[[ c ]]]
    | (c :: cs) =>
      flat_map (fun ps => [ athead c ps ; [c] :: ps ])
               (filter non_empty (parts cs))
    end.

  Lemma parts_append_correct
    : forall xs yss, In yss (parts xs) -> concat yss = xs.
  Proof.
    induction xs ; intros.
    +
      simpl in *. crush.
    +
      simpl in *. destruct xs. simpl in *. crush.
      apply in_flat_map in H.
      destruct H as [y [HIny HInyss]].
      apply filter_In in HIny.
      destruct HIny.
      apply non_empty_true in H0.
      destruct H0 as [z [zs Heq]].
      substs.
      apply IHxs in H.
      rewrite <- H.
      simpl in HInyss.
      crush.
  Qed.

  Lemma empty_app_both_empty 
    : forall (xs ys : list A), [] = xs ++ ys -> xs = [] /\ ys = [].
  Proof.
    induction xs ; destruct ys ; intros ; crush.
  Qed.

  Lemma concat_empty
    : forall (yss : list (list A)), concat yss = [] -> Forall (fun ys => ys = []) yss.
  Proof.
    induction yss ; crush.
    constructor ;
    symmetry in H ;
    apply empty_app_both_empty in H ; destruct* H.
  Qed.

  Lemma parts_empty
    : forall (xs : list A), In [[]] (parts xs) -> xs = [].
  Proof.
    intros xs H ; apply parts_append_correct in H ; crush.
  Qed.

 End PARTS.

Section FORALL.

  Variable A : Type.

  Lemma forallb_Forall
    : forall (xs : list A) f, forallb f xs = true <-> Forall (fun x => f x = true) xs.
  Proof.
    induction xs ; intro f ; splits ; intros ; crush.
    +
      apply andb_prop in H. destruct H.
      apply IHxs in H0.
      constructor ; auto.
    +
      inverts* H.
      apply IHxs in H3.
      crush.
  Qed.
End FORALL.

Section EXISTS.

  Variable A : Type.

  Lemma existsb_Exists
    : forall (xs : list A) f, existsb f xs = true <-> Exists (fun x => f x = true) xs.
  Proof.
    induction xs ; intros f ; splits ; intros H ; simpl in * ; inverts H.
    +
      apply orb_prop in H1.
      destruct* H1. constructor ; rewrite H ; auto.
      rewrite H.
      rewrite orb_true_r.
      apply Exists_cons.
      right*. apply IHxs in H. auto.
    +
      crush.
    +
      apply IHxs in H1.
      rewrite H1.
      rewrite orb_true_r.
      auto.
  Qed.
End EXISTS.


Section OPTION.
  Variable A : Type.

  Definition is_some (v : option A) : bool :=
    match v with
    | Some _ => true
    | _      => false
    end.

End OPTION.