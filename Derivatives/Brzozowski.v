(** Brzozowski derivatives and its properties *)

Set Implicit Arguments.

Require Import
        Syntax.Regex
        Derivatives.Smart
        Program.

Fixpoint deriv (a : ascii)(e : regex) : regex :=
  match e with
  | #0 => #0
  | #1 => #0
  | $ c =>
    match ascii_dec a c with
    | left _ => #1
    | right _ => #0              
    end
  | (e1 @ e2) =>
    match null e1 with
    | left _ =>
      ((deriv a e1) :@: e2) :++: (deriv a e2)
    | right _ =>
      (deriv a e1) :@: e2
    end  
  | (e1 :+: e2) =>
    (deriv a e1) :++: (deriv a e2)
  | (e1 ^*) =>
     (deriv a e1) :@: (e1 :^*:)
  end.  

Theorem deriv_sound
  : forall e a s
  , s <<- (deriv a e)
    -> (String a s) <<- e.
Proof.
  induction e ; intros a' s H ; simpl in * ; try solve [ inverts* H ] ;
    repeat (match goal with
            | [H : _ <<- #0 |- _] =>
              inverts* H
            | [H : _ <<- #1 |- _] =>
              inverts* H
            | [H : context[if ?E then _ else _] |- _] =>
               destruct* E
            end ; substs*).
  +
    lets J : choice_smart_sound H.
    inverts* J.
    lets K : cat_smart_sound H2.
    inverts* K.
  +
    lets J : cat_smart_sound H.
    inverts* J.
  +
    lets J : choice_smart_sound H.
    inverts* J.
  +
    lets J : cat_smart_sound H.
    inverts* J.
    lets K : star_smart_sound H4.
    rewrite str_append_rewind.
    inverts* K.
    econstructor ; eauto.
Qed.
(*            
Lemma deriv_star_complete
  : forall e a s
  , (String a s) <<- e          
  -> s <<- deriv a e.               
Proof.
  refine (fix lemm e a s prf {struct prf} : s <<- deriv a e := _).
  inverts prf ; simpl in * ;
    repeat (match goal with
            | [H : context[if ?E then _ else _] |- _] =>
              destruct E
            | [|- context[if ?E then _ else _]] =>
              destruct E
            | [H : ?a <> ?a |- _] =>
              elim H ; reflexivity
            | [|- _] => constructor
            end).
  +
    destruct s0.
    -
      simpl in *.
      substs.
      apply choice_smart_complete.
      apply InRight.
      apply lemm.
      assumption.
    -
      inverts H1.
      apply choice_smart_complete.
      apply InLeft.
      apply cat_smart_complete.
      econstructor.
      eapply lemm.
      eassumption.
      eassumption.
      reflexivity.
  +     
    destruct s0.
    -
      contradiction.
    -
      inverts H1.
      apply cat_smart_complete.
      econstructor.
      eapply lemm.
      eassumption.
      eassumption.
      reflexivity.
  +     
    apply choice_smart_complete ;
      apply InLeft ; apply lemm ; assumption.
  +
    apply choice_smart_complete ;
      apply InRight ; apply lemm ; assumption.
  +
    inverts H.
    - now inverts H2.
    -
      inverts H2.
      apply cat_smart_complete.
      eapply InCat.
      apply lemm.
Qed.


  *)

  
Theorem deriv_complete
  :  forall e a s
  ,  (String a s) <<- e
  -> s <<- deriv a e.
Proof.
  induction e ; intros a' s H ; simpl in * ;
    repeat (match goal with
            | [H : _ <<- #0 |- _] =>
              inverts* H
            | [H : _ <<- #1 |- _] =>
              inverts* H
            | [H : _ <<- ($ _) |- _] =>
              inverts* H
            | [H : context[if ?E then _ else _] |- _] =>
              destruct* E
            | [|- context[if ?E then _ else _]] =>
              destruct* E
            | [H : ?a <> ?a |- _] =>
              elim H ; reflexivity
            end ; substs*). 
  +
    inverts* H.
    destruct* s0.
    - 
      simpl in *. substs*.
      apply choice_smart_complete.
      apply InRight ; auto.
    -
      inverts* H5.
      apply choice_smart_complete.
      apply InLeft.
      apply cat_smart_complete ; eauto.
  +
    inverts* H.
    apply cat_smart_complete.
    destruct* s0.
    -
      contradiction.
    -
      inverts* H5.
  +
    apply choice_smart_complete.
    inverts* H.
  +
    inverts* H.
    inverts* H2.
    - now inverts* H1.
    -  
      inverts* H1.
      apply cat_smart_complete.
      
Qed.    



                