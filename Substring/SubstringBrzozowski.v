Set Implicit Arguments.

Require Import
        Syntax.Regex
        Derivatives.Brzozowski
        Prefix.PrefixDef
        Prefix.PrefixBrzozowski
        Substring.SubstringDef
        Tactics.Tactics.


Definition brzozowski_substring : forall e s, {substring e s} + {~ substring e s}.
  refine (fix substring_brzozowski e s : {substring e s} + {~ substring e s} :=
            match s with
            | EmptyString =>
              match null e with
              | left _ => left _
              | right _ => right _
              end
            | String a' s' =>
              match brzozowski_prefix e (String a' s') with
              | left _ => left _
              | right _ =>
                match substring_brzozowski e s' with
                | left _ => left _
                | right _ => right _
                end
              end
            end) ; clear substring_brzozowski.
  +
    apply MkSubstring with (xs := "")(ys := "")(zs := "") ; eauto.
  +
    intro contra ; inverts* contra.
    apply empty_string_concat in H0. destruct H0.
    symmetry in H1 ; apply empty_string_concat in H1.
    destruct H1 ; substs ; contradiction.
  +
    apply prefix_is_substring in p.
    inverts* p.
  +
    inverts* s0.
    apply MkSubstring with (xs := String a' xs)(ys := ys)(zs := zs) ; auto.
  +
    apply not_cons_substring ; auto.
Defined.