Set Implicit Arguments.

Require Import
        List
        Syntax.Regex
        Utils.Functions.ListUtils
        Utils.Functions.StringUtils.


Fixpoint accept (e : regex)(s : string) : bool :=
  match e with
  | #0 => false
  | #1 => if string_dec s "" then true else false
  | $ c =>
    match s with
    | String c' EmptyString =>
      if ascii_dec c c' then true else false
    | _ => false
    end
  | e1 :+: e2 => accept e1 s || accept e2 s
  | e1 @ e2 => existsb (fun p => accept e1 (fst p) && accept e2 (snd p))
                      (splits_string s)
  | e ^* => existsb (fun ys => forallb (fun y => accept e y) ys) (parts_string s)
  end.

Lemma accept_cat
  : forall e e' s s', accept e s = true ->
                 accept e' s' = true ->
                 accept (e @ e') (s ++ s') = true.
Proof.
  intros. simpl.
  apply existsb_Exists.
  apply Exists_exists.
  exists (s,s') ; splits*.
  Search splits_string.
  apply append_splits_string_correct  with (s := (s ++ s')) ; auto.
  crush.
Qed.

Hint Resolve accept_cat.

Lemma accept_sound
  : forall e s, accept e s = true -> s <<- e.
Proof.
  induction e ; intros s H ; crush.
  +
    destruct (string_dec s "") ; crush.
  +
    destruct s ; crush. destruct s ; crush.
    destruct (ascii_dec a a0) ; crush.
  +
    apply existsb_Exists in H.
    apply Exists_exists in H.
    destruct H as [[s1 s2] [Hin Hacc]].
    simpl in *.
    apply andb_prop in Hacc.
    destruct Hacc.
    lets J : IHe1 H.
    lets K : IHe2 H0.
    apply splits_string_correct in Hin.
    rewrite <- Hin.
    eapply InCat ; eauto.
  +
    apply orb_prop in H.
    destruct H.
    lets* J : IHe1 H.
    lets* K : IHe2 H.
  +
    apply existsb_Exists in H.
    apply Exists_exists in H.
    destruct H as [x [Hin Hfa]].
   
Admitted.

Lemma accept_complete
  : forall e s, s <<- e -> accept e s = true.
Proof.
  induction e ; intros s H ; inverts* H.
  +
    simpl ; destruct (ascii_dec a a) ; crush.
Admitted.
    