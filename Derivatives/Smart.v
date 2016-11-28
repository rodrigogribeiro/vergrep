(** smart constructors *)

Set Implicit Arguments.

Require Import
        Syntax.Regex.

(* choice *)

Fixpoint choice_smart (e e' : regex) : regex :=
  match e, e' with
  | #0, e2 => e2
  | e1, #0 => e1
  | e1, e2 => e1 :+: e2               
  end.

Notation "e1 ':++:' e2" := (choice_smart e1 e2)(at level 40, left associativity).

Lemma choice_smart_sound : forall e1 e2 s, s <<- (e1 :++: e2) -> s <<- (e1 :+: e2).
Proof.
  induction e1 ; destruct e2 ; intros s H ; inverts* H ; auto.
Qed.

Lemma choice_smart_complete : forall e1 e2 s, s <<- (e1 :+: e2) -> s <<- (e1 :++: e2).
Proof.
  induction e1 ; destruct e2 ; simpl in * ; intros s H ; try inverts* H ; try inverts_in_regex.
Qed.

(* concatenation *)

Fixpoint cat_smart (e e' : regex) : regex :=
  match e, e' with
  | #0 , e2 => #0
  | #1 , e2 => e2
  | e1 , #0 => #0
  | e1 , #1 => e1
  | e1 , e2 => e1 @ e2                
  end.

Notation "e1 ':@:' e2" := (cat_smart e1 e2)(at level 40, left associativity).

Lemma cat_smart_sound : forall e1 e2 s, s <<- (e1 :@: e2) -> s <<- (e1 @ e2).
Proof.
  induction e1 ; destruct e2 ; simpl in * ;
    intros s H ; try inverts_in_regex ;
      eauto ; try solve [ econstructor ; eauto ;
                          rewrite str_append_nil_end ; eauto ].
Qed.  

Lemma cat_smart_complete : forall e1 e2 s, s <<- (e1 @ e2) -> s <<- (e1 :@: e2).
Proof.
  induction e1 ; destruct e2 ; simpl in * ;
    intros s H ; try inverts* H ;
      repeat (match goal with
           | [ H : _ <<- #0 |- _ ] =>
             inverts* H
           | [H : _ <<- #1 |- _] =>
             inverts* H
           | [|- context[_ ++ ""]] =>
             rewrite str_append_nil_end ; auto
           end).
Qed.

(* star *)

Fixpoint star_smart (e : regex) : regex :=
  match e with
  | #0 => #1
  | #1 => #1
  | e1 => e1 ^*         
  end.

Notation "e ':^*:'" := (star_smart e)(at level 40, left associativity).
  
Lemma star_smart_sound : forall e s, s <<- (e :^*:) -> s <<- (e ^*).
Proof.
  induction e ; intros s H ; inverts* H.
Qed.  

Lemma star_lemma : forall s,
    s <<- (#1 ^*) -> s = "".
Proof.
 refine (fix star_lemma s prf {struct prf} : s = "" := _).
  inversion_clear prf; subst.
  inversion_clear H; subst.
  - now inversion H0.
  - inversion_clear H0; subst. inversion_clear H; subst.
    rewrite (star_lemma s' H1).
    reflexivity.
Qed.

Lemma star_smart_complete : forall e s, s <<- (e ^*) -> s <<- (e :^*:).
Proof.
  intros e s H ; destruct e ; simpl in * ; inverts* H.
  +
    inverts* H2.
    inverts* H1.
    inverts* H2.
  +
    lets J : InStar H2.
    apply star_lemma in J.
    substs*.
Qed.