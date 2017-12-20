Set Implicit Arguments.

Require Import
        Syntax.Regex
        Derivatives.Brzozowski
        Prefix.PrefixDef
        Tactics.Tactics.


Definition brzozowski_prefix
  : forall e s, {prefix e s} + {~ prefix e s}.
  Hint Resolve empty_not_prefix cons_not_prefix_brzozowski.
  refine (fix brzozowski_prefix e s : {prefix e s} + {~ prefix e s} :=
            match s with
            | EmptyString =>
              match null e with
              | left _ => left _
              | right _ => right _
              end
            | String a s' =>
              match null e with
              | left _ => left _
              | right _ => 
                match brzozowski_prefix (deriv a e) s' with
                | left _ => left _
                | right _ => _
                end
              end
            end) ; clear brzozowski_prefix ;
    try solve [econstructor ; eauto ; reflexivity].
  +
    intro H ; inverts* H.
    apply empty_string_concat in H1.
    destruct* H1. substs ; contradiction.
  +
    inverts* p.
    eapply deriv_sound in H; eauto.
    simpl in * ; econstructor ; eauto. reflexivity.
Defined.