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

Lemma string_to_list_app
  : forall s s', string_to_list (s ++ s') = (string_to_list s) ++ (string_to_list s').
Proof.
  induction s ; destruct s' ; crush.
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

Lemma list_to_string_inj
  : forall xs ys, list_to_string xs = list_to_string ys -> xs = ys.
Proof.
  induction xs ; destruct ys ; crush ; fequals*.
Qed.

Lemma list_to_string_empty
  : forall xs, list_to_string xs = EmptyString -> xs = [].
Proof.
  induction xs ; crush.
Qed.

Lemma string_to_list_list_to_string
  : forall xs, string_to_list (list_to_string xs) = xs.
Proof.
  induction xs ; crush.
Qed.

Lemma string_to_list_empty
  : forall s, string_to_list s = [] -> s = EmptyString.
Proof.
  induction s ; crush.
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
    apply parts_append_correct in HIn ; auto.
    substs. rewrite <- (string_to_list_list_to_string (concat x)) in HIn.
    eapply string_to_list_inj in HIn.
    rewrite list_to_string_concat in HIn.
    auto.
  Qed.

  Lemma map_to_string_empty
    : forall xs, map list_to_string xs = [""] -> xs = [[]].
  Proof.
    induction xs ; intros H ; simpl in * ; try discriminate.
    inverts* H.
    apply map_eq_nil in H2.
    substs. apply list_to_string_empty in H1 ; substs*.
  Qed.

  Lemma parts_string_empty
    : forall s, In [""] (parts_string s) -> s = "".
  Proof.
    pose ascii_dec as K.
    intros ; unfold parts_string in *.
    apply in_map_iff in H.
    destruct H as [x [Heq Hin]].
    apply parts_append_correct in Hin ; auto.
    apply map_to_string_empty in Heq.
    substs. simpl in *. symmetry in Hin.
    apply string_to_list_empty in Hin ; auto.
  Qed.

End PARTS_STRING.

Section SPLIT_STRING.

  Definition splits_string (s : string) :=
    map (fun p => (list_to_string (fst p), list_to_string (snd p)))
        (splits (string_to_list s)).

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

  Lemma append_splits_string_correct
    : forall s s1 s2, s = (s1 ++ s2)%string -> In (s1,s2) (splits_string s).
  Proof.
    unfold splits_string.
    intros s s1 s2 Heq.
    rewrite <- list_to_string_string_to_list in Heq.
    rewrite <- (list_to_string_string_to_list s) in Heq.
    eapply list_to_string_inj in Heq.
    rewrite string_to_list_app in Heq.
    apply append_splits_correct in Heq.
    apply in_map_iff.
    exists ((string_to_list s1), (string_to_list s2)) ; crush.
    fequals ; apply list_to_string_string_to_list.
  Qed.
End SPLIT_STRING.