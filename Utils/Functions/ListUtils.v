Set Implicit Arguments.

Require Import
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

  Fixpoint parts (xs : list A) : list (list (list A)) :=
    match xs with
    | [] => [[]]
    | [ c ] => [[[ c ]]]
    | (c :: cs) =>
      concat (map (fun ps => [ athead c ps ; [c] :: ps ]) (filter non_empty(parts cs)))
    end.

End PARTS.