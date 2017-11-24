(** Brzozowski derivatives and its properties *)

Set Implicit Arguments.

Require Import
        Syntax.Regex
        Derivatives.Smart.

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
  Local Hint Resolve
        cat_smart_sound
        cat_smart_complete
        choice_smart_sound
        choice_smart_complete
        star_smart_sound
        star_smart_complete.
  induction e ; intros a' s H ; simpl in * ; try solve [ inverts* H ] ;
    repeat (match goal with
            (** empty case *)  
            | [H : _ <<- #0 |- _] =>
              inverts* H
            (** lambda case *) 
            | [H : _ <<- #1 |- _] =>
              inverts* H
            (** breaking the conditional on concatenation *)
            | [H : context[if ?E then _ else _] |- _] =>
              destruct* E
            (** choice case *)              
            | [H : _ <<- (_ :++: _) |- _] =>
              lets J : choice_smart_sound H ;
              clear H ; inverts* J
            (** concatenation case *)                        
            | [H : _<<- (_ :@: _) |- _] =>
              lets J : cat_smart_sound H ; clear H ; inverts* J
            end ; substs*).
Qed.

Hint Resolve deriv_sound.
            
Theorem deriv_complete
  :  forall e a s
  ,  (String a s) <<- e
  -> s <<- deriv a e.
Proof.
  Local Hint Immediate
        cat_smart_sound
        cat_smart_complete
        choice_smart_sound
        choice_smart_complete
        star_smart_sound
        star_smart_complete.
  induction e ; intros a' s H ; simpl in * ; try inverts* H ;
    repeat (match goal with
            (** empty case *)  
            | [H : _ <<- #0 |- _] =>
              inverts* H
            (** lambda case *)             
            | [H : _ <<- #1 |- _] =>
              inverts* H
            (** character case *)             
            | [H : _ <<- ($ _) |- _] =>
              inverts* H
            (** concatenation *)             
            | [H : context[if ?E then _ else _] |- _] =>
              destruct* E
            | [|- context[if ?E then _ else _]] =>
              destruct* E                         
            | [H : ?a <> ?a |- _] =>
              elim H ; reflexivity
            | [H : String _ _ = ?s ++ _  |- _ <<- (_ :++: _)] =>
              apply choice_smart_complete ; destruct* s 
            | [H : String _ _ = String _ _ |- _] => inverts* H
            | [H  : "" <<- ?e,
               H1 : String _ _ = "" ++ _ |- _ <<- (deriv _ ?e :@: _) :+: _] =>
              simpl in * ; apply InRight ; auto
            | [ H : String _ _ = (String ?a ?s) ++ _
              , H1 : (String ?a ?s) <<- ?e |-
                _ <<- (deriv _ ?e :@: _) :+: _] =>
              simpl in * ; apply InLeft ; apply cat_smart_complete ; eauto
            (** star case *)                                                           
            | [H : String _ _ = ?s ++ _ |- _ <<- (_ :@: _)] =>
              destruct* s ; simpl in * ; apply cat_smart_complete ;
              try contradiction ; eauto
            end ; substs*).
Qed.    

Hint Immediate deriv_complete.            
