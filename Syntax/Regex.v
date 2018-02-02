(** Definition of regular expression syntax *)

Set Implicit Arguments.

Require Export
        Tactics.Tactics
        Relation_Definitions
        Setoid
        List
        Omega
        Bool
        Coq.Structures.Orders
        Ascii
        String.

Import ListNotations.

Open Scope string_scope.

Inductive regex : Set :=
| Emp : regex  
| Eps : regex          
| Chr : ascii -> regex
| Cat : regex -> regex -> regex
| Choice : regex -> regex -> regex
| Star : regex -> regex.                               

Notation "'#0'" := Emp.
Notation "'#1'" := Eps.
Notation "'$' c" := (Chr c)(at level 40).
Notation "e '@' e1" := (Cat e e1)(at level 15, left associativity).
Notation "e ':+:' e1" := (Choice e e1)(at level 20, left associativity).
Notation "e '^*'" := (Star e)(at level 40).
  
(** Semantics of regular expressions *)

Reserved Notation "s '<<-' e" (at level 40).

Inductive in_regex : string -> regex -> Prop :=
| InEps
  : EmptyString <<- #1
| InChr
  : forall c
  , String c EmptyString <<- ($ c)
| InCat
  :  forall e e' s s' s1
  ,  s <<- e
  -> s' <<- e'
  -> s1 = s ++ s'
  -> s1 <<- (e @ e')
| InLeft
  :  forall s e e'
  ,  s <<- e
  -> s <<- (e :+: e')
| InRight
  :  forall s' e e'
  ,  s' <<- e'
  -> s' <<- (e :+: e')
| InStarLeft
  : forall e
  , EmptyString <<- (e ^*)
| InStarRight              
  : forall s s' s1 a e
  ,  (String a s) <<- e
  -> s' <<- (e ^*)
  -> s1 = String a (s ++ s')
  -> s1 <<- (e ^*)                          
where "s '<<-' e" := (in_regex s e).

Hint Constructors in_regex.

Ltac inverts_in_regex :=
  match goal with
  | [H : _ <<- _ |- _] => inverts H  
  end.

Lemma empty_string_concat
  : forall (s s' : string)
  , "" = s ++ s'
  -> s = "" /\ s' = "".
Proof.
  intros ; destruct s ; destruct s' ; splits ; simpl in * ; try congruence.
Qed.

Lemma str_append_nil_end
  : forall (s : string), s ++ "" = s.
Proof.
  induction s ; simpl in * ; [idtac | rewrite IHs ] ; eauto.
Qed.

Hint Resolve empty_string_concat.

(** nullability test *)

Fixpoint null (e : regex) : bool :=
  match e with
  | #0 => false
  | #1 => true
  | $ _ => false
  | e1 @ e2 =>
    andb (null e1) (null e2)
  | e1 :+: e2 =>
    orb (null e1) (null e2)
  | (_ ^*) =>
     true
  end.

Theorem null_sound : forall e, Is_true(null e) -> "" <<- e.
Proof.
  induction e ; intros ; simpl in * ; crush.
  +
    lets J : andb_prop_elim H.
    destruct* J.
  +
    lets J : orb_prop_elim H.
    destruct* J.
Qed.

Theorem null_complete : forall e, "" <<- e -> Is_true (null e).
Proof.
  intros e H ; induction e ; inverts* H ; simpl in * ; crush.
  +
    apply empty_string_concat in H5 ; destruct H5 ; substs ;
    apply andb_prop_intro ; splits*.
  +
    apply orb_prop_intro. left*.
  +
    apply orb_prop_intro. right*.
Qed.

(* size *)

Fixpoint size (e : regex) : nat :=
  match e with
  | e1 :+: e2 => 1 + max (size e1) (size e2)
  | e1 @ e2 => 1 + max (size e1) (size e2)
  | Star e => 1 + size e
  | _ => 1
  end.

(** equivalence *)

Definition regex_equiv (e e' : regex) : Prop :=
  forall s, s <<- e <-> s <<- e'.

Lemma regex_equiv_refl : Reflexive regex_equiv.
Proof.
  unfolds ; unfolds regex_equiv ; intros ; splits ; auto.
Qed.

Lemma regex_equiv_sym : Symmetric regex_equiv.
Proof.  
  unfolds ; unfolds regex_equiv ; intros x y H s ; splits ; intros H1 ;
  lets J : H s ; destruct* J.
Qed.

Lemma regex_equiv_trans : Transitive regex_equiv.
Proof.
  unfolds ; unfolds regex_equiv ; intros x y z H1 H2 s ; splits ; intros H3 ;
  lets J : H1 s ;
  lets K : H2 s ;
  destruct* J ; destruct* K.
Qed.

Instance regex_equiv_Equiv : Equivalence regex_equiv.
Proof.
  split ;
    [ apply regex_equiv_refl
    | apply regex_equiv_sym
    | apply regex_equiv_trans ].
Qed.

Definition regex_eq_dec (e e' : regex) : {e = e'} + {e <> e'}.
  pose ascii_dec.
  decide equality.
Defined.  

(* regex is an decidable type *)

Module Regex_as_DT <: UsualDecidableType.

  Definition t := regex.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition eq_dec := regex_eq_dec.
  Definition eq_equiv : Equivalence eq.
  Proof.
    split ; unfolds ;
      [ apply eq_refl
      | apply eq_sym
      | apply eq_trans ].
  Defined.  
End Regex_as_DT.

(* ordering relation for regex *)

