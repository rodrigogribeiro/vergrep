Set Implicit Arguments.

Require Import
        Syntax.Regex
        Utils.AsciiOT
        Structures.Orders.


Module RegexOT <: Orders.OrderedType.
  Definition t := regex.

  Definition eq := @eq regex.
  Definition eq_refl := @eq_refl regex.
  Definition eq_sym := @eq_sym regex.
  Definition eq_trans := @eq_trans regex.

  Definition eq_dec := regex_eq_dec.

  Inductive lt_regex : regex -> regex -> Prop :=
  | Empty_Eps_lt : lt_regex #0 #1
  | Empty_Chr_lt : forall c, lt_regex #0 ($ c)
  | Empty_Cat_lt : forall e e', lt_regex #0 (e @ e')
  | Empty_Choice_lt : forall e e', lt_regex #0 (e :+: e')
  | Empty_Star_lt : forall e, lt_regex #0 (e ^*) 
  | Eps_chr_lt : forall c, lt_regex #1 ($ c)
  | Eps_cat_lt : forall e e', lt_regex #1 (e @ e')
  | Eps_choice_lt : forall e1 e2, lt_regex #1 (e1 :+: e2)
  | Eps_star_lt : forall e, lt_regex #1 (e ^*)
  | Chr_chr_lt : forall c c', AsciiOT.lt c c' -> lt_regex ($ c) ($ c')
  | Chr_cat_lt : forall c e e', lt_regex ($ c) (e @ e')
  | Chr_choice_lt : forall c e e', lt_regex ($ c) (e :+: e')
  | Chr_star_lt : forall c e, lt_regex ($ c) (e ^*)
  | Cat_cat_ltr : forall e1 e2 e2', lt_regex e2 e2' ->
                               lt_regex (e1 @ e2) (e1 @ e2')
  | Cat_cat_ltl : forall e1 e2 e1' e2', lt_regex e1 e1' ->
                                   lt_regex (e1 @ e2) (e1' @ e2')
  | Cat_choice_lt : forall e1 e2 e1' e2', lt_regex (e1 @ e2) (e1' :+: e2')
  | Cat_star_lt   : forall e1 e2 e, lt_regex (e1 @ e2) (e ^*)
  | Choice_choice_ltr : forall e1 e2 e2', lt_regex e2 e2' ->
                               lt_regex (e1 :+: e2) (e1 :+: e2')
  | Choice_choice_lt : forall e1 e2 e1' e2', lt_regex e1 e1' ->
                                        lt_regex (e1 :+: e2) (e1' :+: e2')
  | Choice_star_lt : forall e1 e2 e, lt_regex (e1 :+: e2) (e ^*)
  | Star_star_lt : forall e e', lt_regex e e' -> lt_regex (e^*) (e' ^*).

  Global Hint Constructors lt_regex.

  Definition lt := lt_regex.

  Lemma lt_regex_trans :
    forall e e' e'', lt e e' -> lt e' e'' -> lt e e''.
  Proof.
    Hint Resolve AsciiOT.lt_trans.
    intros e e' e'' H ; generalize dependent e'' ; induction H ;
      intros e22 He22 ; inverts* He22 ; try solve [econstructor ; eauto] ;
        try solve [lets J: IHlt_regex H3 ; econstructor ; eauto] ;
          try solve [lets J: IHlt_regex H1 ; econstructor ; eauto ].
  Qed.

  Lemma lt_regex_not_eq
    : forall e e', lt e e' -> e <> e'.
  Proof.
    Hint Resolve AsciiOT.lt_not_eq.
    intros e e' H contra ; induction H ;
      try congruence ; inverts* contra ; inverts* H.
    destruct (N.compare_lt_iff (N_of_ascii c') (N_of_ascii c')).
    apply H in H1.
    apply N.lt_irrefl in H1. auto.
  Qed.

  Fixpoint compare (e e' : regex) : comparison :=
    match e,e' with
    | #0 , #0 => Eq
    | #0 , _  => Lt
    | _  , #0 => Gt
    | #1 , #1 => Eq
    | #1 , _  => Lt
    | _  , #1 => Gt
    | $ a, $ b =>
      match AsciiOT.compare a b with
      | LT _ => Lt
      | EQ _ => Eq
      | GT _ => Gt
      end
    | $ _ , _ => Lt
    | _   , $ _ => Gt
    | e1 @ e2, e1' @ e2' =>
      match compare e1 e1', compare e2 e2' with
      | Lt , _  => Lt
      | Eq , Lt => Lt
      | Eq , Eq => Eq
      | Eq , Gt => Gt
      | Gt , _ => Gt
      end
    | _ @ _ , _ :+: _ => Lt
    | _ @ _ , _ ^* => Lt
    | _ :+: _ , _ @ _ => Gt
    | _ ^* , _ @ _ => Gt
    | e1 :+: e2, e1' :+: e2' =>
      match compare e1 e1', compare e2 e2' with
      | Lt , _  => Lt
      | Eq , Lt => Lt
      | Eq , Eq => Eq
      | Eq , Gt => Gt
      | Gt , _ => Gt
      end
    | _ :+: _, _ ^* => Lt
    | _ ^* , _ :+: _ => Gt 
    | e ^* , e' ^* => compare e e'
    end.

    Definition lt_trans := lt_regex_trans.
    Definition lt_not_eq := lt_regex_not_eq.

    Definition eq_equiv := Regex_as_DT.eq_equiv.
    
    Definition lt_strorder : StrictOrder lt.
      split ; unfolds ; unfold lt, Reflexive, complement.
      intros x H ; lets K : lt_not_eq x x H ; contradiction.
      apply lt_trans.
    Defined.

    Definition lt_compat : Proper (eq==> eq ==> iff) lt.
      split ; unfold eq, lt in * ; intros ; substs*.
    Defined.

    Lemma compare_refl : forall e, compare e e = Eq.
    Proof.
      induction e ; simpl ; auto ;
        repeat (match goal with
                | [|- context[match ?E with _=>_ end]] => destruct E
                | [H : AsciiOT.lt ?a ?a |- _] =>
                  apply AsciiOT.lt_not_eq in H ;
                  unfold AsciiOT.eq in * ; try contradiction
                end ; eauto) ; try congruence.
    Defined.

    Lemma compare_lt : forall e e', lt e e' -> compare e e'  = Lt.
    Proof.
      induction e ; intros e' H ; inverts* H ; simpl.
      destruct (AsciiOT.compare a c') eqn:Heqn ; eauto.
      unfold AsciiOT.lt, AsciiOT.eq in *.
      subst. apply N.lt_irrefl in H1. contradiction.
      lets J : N.lt_trans H1 l.
      apply N.lt_irrefl in J ; contradiction.
      rewrite compare_refl.
      apply IHe2 in H3. rewrite H3 ; auto.
      rewrite (IHe1 _ H3) ; auto.
      rewrite compare_refl.
      rewrite (IHe2 _ H3) ; auto.
      rewrite (IHe1 _ H3) ; auto.
    Qed.

    Lemma compare_gt : forall e e', lt e' e -> compare e e' = Gt.
    Proof.
      induction e ; intros e' H ; inverts* H ; simpl.
      +
        destruct (AsciiOT.compare a c) eqn:Heqn ; eauto.
        unfold AsciiOT.lt, AsciiOT.eq in *.
        clear Heqn.
        lets J : N.lt_trans H2 l.
        apply N.lt_irrefl in J. contradiction.
        clear Heqn.
        unfold AsciiOT.lt, AsciiOT.eq in *.
        subst.
        lets J : N.lt_irrefl H2. contradiction.
      +
        rewrite compare_refl.
        lets J : IHe2 H2.
        rewrite J ; auto.
      +
        lets J : IHe1 H2.
        rewrite J ; auto.
      +
        rewrite compare_refl.
        lets J : IHe2 H2.
        rewrite J ; auto.
      +
        lets J : IHe1 H2.
        rewrite J ; auto.
    Qed.

    Definition compare_spec : forall e e', CompareSpec (eq e e')
                                                  (lt e e')
                                                  (lt e' e)
                                                  (compare e e').
      induction e ; intros e' ; destruct e' ;
        unfold eq, lt in * ;
          repeat (match goal with
                  | [|- context[match ?E with _ => _ end]] =>
                    destruct E ; unfold AsciiOT.eq in * ; substs
                  | [|- context[CompareSpec (?e = ?e) _ _ _]] =>
                    apply CompEq ; eauto
                  | [|- context[CompareSpec (#0 = _) _ _ _]] =>
                    apply CompLt ; eauto
                  | [|- context[CompareSpec (_ = #0) _ _ _]] =>
                    apply CompGt ; eauto
                  | [|- context[CompareSpec (#1 = ?e) _ _ _]] =>
                    apply CompLt ; eauto
                  | [|- context[CompareSpec (?e = #1) _ _ _]] =>
                    apply CompGt ; eauto
                  | [|- context[CompareSpec ($ ?a = $ ?b) _ _ _]] =>
                    simpl ; destruct (AsciiOT.compare a a0) ;
                      unfold AsciiOT.eq in * ; 
                       [ apply CompLt
                       | apply CompEq
                       | apply CompGt ] ; substs*
                  | [|- context[CompareSpec ($ _ = _) _ _ _]] =>
                    apply CompLt ; eauto
                  | [|- context[CompareSpec (_ = $ _) _ _ _]] =>
                    apply CompGt ; eauto
                  | [|- context[CompareSpec ((_ @ _) = (_ :+: _)) _ _ _]] =>
                    apply CompLt ; eauto
                  | [|- context[CompareSpec ((_ :+: _) = (_ @ _)) _ _ _]] =>
                    apply CompGt ; eauto
                  | [|- context[CompareSpec ((_ @ _) = (_ ^*)) _ _ _]] =>
                     apply CompLt ; eauto
                  | [|- context[CompareSpec ((_ ^*) = (_ :+: _)) _ _ _]] =>
                     apply CompGt ; eauto
                  | [|- context[CompareSpec ((_ ^*) = (_ @ _)) _ _ _]] =>
                     apply CompGt ; eauto
                  | [|- context[CompareSpec ((_ :+: _) = (_ ^*)) _ _ _]] =>
                    apply CompLt ; eauto
                  end).
      +
        lets J: IHe1 e'1.
        lets K: IHe2 e'2.
        destruct J ; destruct K ; simpl in * ; substs.
        rewrite compare_refl ; rewrite compare_refl ; eauto.
        rewrite compare_refl.
        apply compare_lt in H0.
        rewrite H0.
        lets K : IHe2 e'2.
        apply CompLt ; eauto.
        rewrite H0 in *.
        inverts* K.
        rewrite compare_refl.
        apply compare_gt in H0.
        rewrite H0.
        lets J : IHe2 e'2.
        rewrite H0 in J.
        inverts* J.
        apply compare_lt in H ; rewrite H.
        lets J : IHe1 e'1. rewrite H in J.
        inverts* J.
        lets J : IHe1 e'1.
        apply compare_lt in H.
        rewrite H in *.
        inverts* J.
        lets J : IHe1 e'1.
        apply compare_lt in H.
        rewrite H in *.
        inverts* J.
        lets J : IHe1 e'1.
        apply compare_gt in H.
        rewrite H in *.
        inverts* J.
        lets J : IHe1 e'1.
        apply compare_gt in H.
        rewrite H in *.
        inverts* J.
        lets J : IHe1 e'1.
        apply compare_gt in H.
        rewrite H in *.
        inverts* J.
    +
        lets J: IHe1 e'1.
        lets K : IHe2 e'2.
        destruct J ; destruct K ; simpl in * ; substs.
        rewrite compare_refl ; rewrite compare_refl ; eauto.
        rewrite compare_refl.
        apply compare_lt in H0.
        rewrite H0.
        lets K : IHe2 e'2.
        apply CompLt ; eauto.
        rewrite H0 in *.
        inverts* K.
        rewrite compare_refl.
        apply compare_gt in H0.
        rewrite H0.
        lets J : IHe2 e'2.
        rewrite H0 in J.
        inverts* J.
        apply compare_lt in H ; rewrite H.
        lets J : IHe1 e'1. rewrite H in J.
        inverts* J.
        lets J : IHe1 e'1.
        apply compare_lt in H.
        rewrite H in *.
        inverts* J.
        lets J : IHe1 e'1.
        apply compare_lt in H.
        rewrite H in *.
        inverts* J.
        lets J : IHe1 e'1.
        apply compare_gt in H.
        rewrite H in *.
        inverts* J.
        lets J : IHe1 e'1.
        apply compare_gt in H.
        rewrite H in *.
        inverts* J.
        lets J : IHe1 e'1.
        apply compare_gt in H.
        rewrite H in *.
        inverts* J.
     +    
       lets J : IHe e'.
       destruct J ; simpl ; substs.
       rewrite compare_refl.
       eauto.
       apply compare_lt in H.
       lets J : IHe e'.
       rewrite H in *.
       inverts* J.
       lets J : IHe e'.
       apply compare_gt in H.
       rewrite H in *.
       inverts* J.
   Defined.
End RegexOT.