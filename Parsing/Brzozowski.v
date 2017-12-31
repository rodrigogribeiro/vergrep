Set Implicit Arguments.

Require Import
        Syntax.Regex
        Derivatives.Brzozowski
        Derivatives.Smart.

(** simple parsing algoritm using Brzozowski derivatives *)

Fixpoint brzozowski (s : string)(e : regex) : regex :=
  match s with
  | "" => e
  | (String a s') =>
    brzozowski s' (deriv a e)
  end.  

Theorem brzozowski_sound
  :  forall s e
  ,  "" <<- (brzozowski s e)
  -> s <<- e.
Proof.
  induction s ; destruct e ; intros ; simpl in * ;
    repeat (match goal with
            (** empty *)  
            | [H : _ <<- #0 |- _] =>
              inverts* H
            (** lambda *)             
            | [H : _ <<- #1 |- _] =>
              inverts* H
            (** character *)              
            | [H : _ <<- ($ _) |- _] =>
              inverts* H
            | [H : ?a <> ?a |- _] =>
              elim H ; reflexivity
            (** concatenation and choice *)             
            | [IHs : forall e, "" <<- brzozowski _ e -> _ <<- e
               , H : "" <<- _ |- _] =>
              lets J : IHs H ; try solve [ inverts* H ] ; clear H
            | [H : _ <<- (_ :++: _) |- _] =>
              lets K : choice_smart_sound H ; clear H
            | [H : _ <<- (_ :+: _) |- _] => inverts* H
            | [H : _ <<- (_ :@: _) |- _] =>
              lets M : cat_smart_sound H ; try inverts* M
            end ; substs* ; simpl in *) ; eauto. 
Qed.

Theorem brzozowski_complete
  :  forall s e
  ,  s <<- e
  -> "" <<- (brzozowski s e).
Proof.
  Local Hint Immediate
        cat_smart_sound
        cat_smart_complete
        choice_smart_sound
        choice_smart_complete
        star_smart_sound
        star_smart_complete.  
  induction s ; destruct e ; intros ; simpl in * ;
    repeat (match goal with
            (* empty *) 
            | [H : _ <<- #0 |- _] =>
              inverts* H
            (* lambda *)             
            | [H : _ <<- #1 |- _] =>
              inverts* H
            (* characters *)              
            | [H : _ <<- ($ _) |- _] =>
              inverts* H
            | [H : ?a <> ?a |- _] =>
              elim H ; reflexivity
            (* induction hypothesis *)
            | [H : forall e, _ <<- e -> "" <<- brzozowski _ e |- _] =>
              eapply IHs
            (* concatenation *)
            | [H : _ <<- (_ @ _) |- _ ] => inverts* H
            | [H : String _ _ = ?s ++ _ |- _ <<- ((_ :@: _) :++: _)] =>
              eapply choice_smart_complete ; destruct* s ;
              simpl in * ; try inverts* H
            | [H : String ?a ?s <<- ?e1,
               H1 : ?s1 <<- ?e2 |- (?s ++ ?s1) <<- _ :+: _] =>
              apply InLeft ; apply cat_smart_complete ; eauto
            | [H : String _ _ = ?s ++ _ |- _ <<- ( _ @ _ )] =>
              destruct* s ; simpl in * ; try contradiction ; inverts* H
            (* choice *)
            | [H : _ <<- (_ :+: _) |- _] => inverts* H
            | [|- _ <<- (_ :++: _)] =>
              eapply choice_smart_complete ; eauto
            | [|- _ <<- (_ :@: _)] =>
              eapply cat_smart_complete ; eauto
            (* star *)
            | [H : (String _ _) <<- (_ ^*) |- _] => inverts* H
            | [H : String _ _ = String _ _ |- _] => inverts* H
               end ; substs* ; eauto) ; eauto.
  +
    destruct (ascii_dec a0 a0) eqn:Heqn ; auto.
    contradiction.
  +
    destruct (null e1) eqn :Heqn.
    apply choice_smart_complete.
    destruct s0 ; simpl in * ; substs.
    apply deriv_complete in H4. auto.
    injects H5. apply deriv_complete in H2.
    apply InLeft. apply cat_smart_complete.
    eapply InCat ; eauto.
    destruct s0 ; simpl in * ; substs.
    apply null_complete in H2. unfolds in H2.
    rewrite Heqn in H2. contradiction.
    injects H5. apply cat_smart_complete.
    apply deriv_complete in H2.
    eapply InCat ; eauto.
Qed.    