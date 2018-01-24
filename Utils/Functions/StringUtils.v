Require Import
        Ascii
        List 
        String
        Utils.Functions.ListUtils
        Tactics.Tactics.

Import ListNotations.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String a' s' => a' :: string_to_list s'
  end.

Lemma string_to_list_inj : forall s s', string_to_list s = string_to_list s' -> s = s'.
Proof.
  induction s ; destruct s' ; crush ; fequals*.
Qed.

Fixpoint list_to_string (xs : list ascii) : string :=
  match xs with
  | [] => EmptyString
  | x :: xs => String x (list_to_string xs)
  end.

Lemma list_to_string_app
  : forall xs ys, list_to_string (xs ++ ys) =
             ((list_to_string xs) ++ (list_to_string ys))%string.
Proof.
  induction xs ; crush.
Qed.

Lemma string_to_list_list_to_string
  : forall xs, string_to_list (list_to_string xs) = xs.
Proof.
  induction xs ; crush.
Qed.

Lemma list_to_string_string_to_list
  : forall s, list_to_string (string_to_list s) = s.
Proof.
  induction s ; crush.
Qed.

Section PARTS_STRING.

  Definition parts_string (s : string) : list (list string) :=
    map (map list_to_string) (parts (string_to_list s)).
  
  Open Scope string_scope.
  
  Definition str_concat (xs : list string) :=
    fold_right append "" xs.
  
  Lemma list_to_string_concat
    : forall x, list_to_string (concat x) = str_concat (map list_to_string x).
  Proof.
    induction x ; crush.
    rewrite <- IHx.
    rewrite list_to_string_app ; auto.
  Qed.
  
  Lemma parts_string_correct
    : forall s yss, In yss (parts_string s) -> str_concat yss = s.
  Proof.
    pose ascii_dec as K.
    unfold parts_string.
    intros s yss H.
    eapply in_map_iff in H.
    destruct H as [x [Heq HIn]].
    apply parts_correct in HIn ; auto.
    substs. rewrite <- (string_to_list_list_to_string (concat x)) in HIn.
    eapply string_to_list_inj in HIn.
    rewrite list_to_string_concat in HIn.
    auto.
  Qed.
End PARTS_STRING.

Section SPLIT_STRING.

  Definition splits_string (s : string) :=
    map (fun p => (list_to_string (fst p), list_to_string (snd p)))
        (splits (string_to_list s)).

  Check splits_append_correct.
  
  Lemma splits_string_correct
    : forall s s1 s2, In (s1,s2) (splits_string s) -> (s1 ++ s2)%string = s.
  Proof.
    unfold splits_string.
    intros s s1 s2 Hin.
    apply in_map_iff in Hin.
    destruct Hin as [[s11 s22] [Heq Hin]].
    simpl in *.
    apply splits_append_correct in Hin.
    injects Heq.
    rewrite <- list_to_string_app.
    rewrite <- list_to_string_string_to_list.
    fequals*.
  Qed.
End SPLIT_STRING.