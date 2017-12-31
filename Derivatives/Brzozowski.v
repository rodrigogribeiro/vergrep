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
    if null e1 then 
      ((deriv a e1) :@: e2) :++: (deriv a e2)
    else 
      (deriv a e1) :@: e2
  | (e1 :+: e2) =>
    (deriv a e1) :++: (deriv a e2)
  | (e1 ^*) =>
     (deriv a e1) :@: (e1 :^*:)
  end.

Lemma choice_inv : forall e e1 e2 s, e = e1 :+: e2 -> s <<- e -> s <<- e1 \/ s <<- e2.
Proof.
  intros e e1 e2 s Heq H ; substs ; inverts* H.
Qed.

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
            | [H: context[ascii_dec ?e ?e'] |- _] =>
              destruct* (ascii_dec e e')
            (** choice case *)              
            | [H : _ <<- (_ :++: _) |- _] =>
              lets J : choice_smart_sound H ;
              clear H ; inverts* J
            (** concatenation case *)                        
            | [H : _<<- (_ :@: _) |- _] =>
              lets J : cat_smart_sound H ; clear H ; inverts* J
            end ; substs*).
            remember (null e1) as N. destruct* N.
            lets J : choice_smart_sound H.
            eapply choice_inv in J ; eauto.
            destruct* J.
            apply cat_smart_sound in H0.
            inverts* H0.
            symmetry in HeqN.
            assert (Hn : "" <<- e1).
               apply null_sound.
               unfolds.
               rewrite HeqN ; auto.
            apply IHe2 in H0 ; eauto.
            apply cat_smart_sound in H.
            inverts* H.
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
            | [ |- context[if (ascii_dec ?e ?e') then _ else _]] =>
              remember (ascii_dec e e') as NN ; destruct* NN ; try contradiction
            end ; substs*).
            destruct s0. simpl in *.
            substs. apply null_complete in H2.
            unfolds in H2. destruct* (null e1). contradiction.
            injects H5. remember (null e1) as NN ; destruct* NN.
            eapply choice_smart_complete.
            apply IHe1 in H2.
            apply InLeft. apply cat_smart_complete ; eauto.
            injects H4.
            apply cat_smart_complete.
            apply IHe in H1.
            eapply InCat ; eauto.
Qed.    

Hint Immediate deriv_complete.            
