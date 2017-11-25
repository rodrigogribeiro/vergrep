Set Implicit Arguments.

Require Import
        Syntax.Regex
        Utils.AsciiOT
        Structures.OrderedType.


Print AsciiOT.

Module RegexOT <: OrderedType.
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
    Search N.compare.
    destruct (N.compare_lt_iff (N_of_ascii c') (N_of_ascii c')).
    apply H in H1.
    apply N.lt_irrefl in H1. auto.
  Qed.

  Lemma compare : forall (e e' : regex), Compare lt_regex eq e e'.
  Proof.
    induction e ; destruct e' ;
      repeat (match goal with
              | [|- Compare _ _ ?e ?e ] =>
                apply EQ ; unfolds ; auto
              | [|- Compare _ _ #0 _] =>
                apply LT ; auto
              | [|- Compare _ _ _ #0] =>
                apply GT ; auto
              | [|- Compare _ _ #1 _] =>
                apply LT ; auto
              | [|- Compare _ _ _ #1] =>
                apply GT ; auto
              | [|- Compare _ _ ($ _) (_ @ _)] =>
                apply LT ; auto
              | [|- Compare _ _ ($ _) (_ :+: _)] =>
                apply LT ; auto
              | [|- Compare _ _ ($ _) (_ ^*)] =>
                 apply LT ; auto
              | [|- Compare _ _ (_ @ _) ($ _)] =>
                apply GT ; auto
              | [|- Compare _ _ (_ @ _) (_ :+: _)] =>
                 apply LT ; auto
              | [|- Compare _ _ (_ @ _) (_ ^*)] =>
                 apply LT ; auto
              | [|- Compare _ _ (_ :+: _) ($ _)] =>
                apply GT ; auto
              | [|- Compare _ _ (_ :+: _) (_ @ _)] =>
                apply GT ; auto
              | [|- Compare _ _ (_ :+: _) (_ ^*)] =>
                 apply LT ; auto
              | [|- Compare _ _ (_ ^*) ($ _)] =>
                 apply GT ; auto
              | [|- Compare _ _ (_ ^*) (_ @ _)] =>
                 apply GT ; auto
              | [|- Compare _ _ (_ ^*) (_ :+: _)] =>
                 apply GT ; auto
              | [|- Compare _ _ ($ ?a) ($ ?a0)] =>
                destruct (AsciiOT.compare a a0) ;
                [ apply LT | apply EQ ; unfolds ; fequals* | apply GT ] ; auto
              end).
              +  
                 lets J : IHe1 e'1 ; 
                 lets K : IHe2 e'2 ; 
                 destruct* J ; destruct* K ;
                   try solve [apply LT ; auto] ;
                   try solve [apply GT ; auto ] ;
                   unfold eq in * ; substs*.
                 econstructor ; eauto.
                 apply EQ ; auto.
                 apply GT ; econstructor ; eauto.
              +
                
                lets J : IHe1 e'1 ;
                  lets K : IHe2 e'2 ;
                  destruct* J ; destruct* K ; unfold eq in * ;
                    substs * ; try solve [apply EQ ; auto] ;
                    try solve [apply LT ; auto] ; 
                    try solve [apply GT ; auto].
              +
                lets J : IHe e'.
                destruct J.
                apply LT ; auto.
                unfold eq in * ; apply EQ ; substs*.
                apply GT ; auto.
     Defined.

     Definition lt_trans := lt_regex_trans.
     Definition lt_not_eq := lt_regex_not_eq.
End RegexOT.