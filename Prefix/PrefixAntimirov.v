Set Implicit Arguments.

Require Import
        List
        String
        Syntax.Regex
        Derivatives.Antimirov
        Prefix.Prefix
        Tactics.Tactics.


Lemma exists_prefix
  : forall E ys zs, Exists (fun e => ys <<- e) E -> Exists (fun e => prefix e (ys ++ zs)) E.
Proof.
  induction E ; intros ys zs H ; inverts* H.
Qed.

Lemma in_prefix
  : forall ys zs E, ys <<<- E -> Exists (fun e => prefix e (ys ++ zs)) E.
Proof.
  intros ys zs E H. unfolds in H.
  apply exists_prefix ; eauto.
Qed.

Hint Resolve in_prefix.

Definition antimirov_prefix
  : forall e s, {prefix e s} + {~ prefix e s}.
  refine (fix antimirov_prefix e s : {prefix e s} + {~ prefix e s} :=
            match s with
            | EmptyString =>
              match null e with
              | left _ => left _
              | right _ => right _
              end
            | String a' s' =>
              match null e with
              | left _ => left _
              | right _ =>
                match Exists_dec (fun e' => prefix e' s')
                                 (pderiv a' e)
                                 (fun e' => antimirov_prefix e' s')
                                 with
                | left _ => left _
                | right _ => right _
                end
              end
            end) ; clear antimirov_prefix ;
               try solve [econstructor ; eauto ; reflexivity ]. 
  +
    intro H ; inverts* H.
    apply empty_string_concat in H1 ; destruct H1 ; substs.
    contradiction.
  +
    apply Exists_exists in e0.
    destruct e0 as [e' [HIe' Hpe']].
    inverts* Hpe'.
    assert (Hex : x <<<- (pderiv a' e)).
    eapply in_set_cons ; eauto.
    eapply pderiv_sound in Hex ; eauto.
    econstructor ; eauto. reflexivity.
  +
    intro contra ; inverts* contra.
    destruct x ; try contradiction.
    injects H0.
    apply pderiv_complete with (s := x) (a := a) in H ; auto.
Defined.