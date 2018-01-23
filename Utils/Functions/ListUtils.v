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

  Lemma splits_correct
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
End SPLITS.

Section PARTS.
  Variable A : Type.

  Fixpoint parts (xs : list A) : list (list (list A)) :=
    match xs with
    | [] => [[[]]]
    | c :: cs =>
      flat_map (fun xss => match xss with
                        | [] => []
                        | p :: ps => [ (c :: p) :: ps ; [ c ] :: p :: ps ] 
                        end) (parts cs)
    end.

  Lemma parts_correct : forall xs xss, In xss (parts xs) -> concat xss = xs.
  Proof.
    induction xs ; intros.
    +
      crush.
    +
      simpl in *.
      destruct (parts xs) eqn : Ha ; simpl in * ; try contradiction.
End PARTS.