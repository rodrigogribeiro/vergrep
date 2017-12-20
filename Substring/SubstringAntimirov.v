Set Implicit Arguments.

Require Import
        String
        Syntax.Regex
        Substring.Substring
        Prefix.Prefix
        Prefix.PrefixAntimirov
        Derivatives.Antimirov
        Tactics.Tactics.


Definition antimirov_substring
  : forall e s, {substring e s} + {~ substring e s}.
  refine (fix antimirov_substring e s : {substring e s} + {~ substring e s} :=
            match s with
            | EmptyString =>
              match null e with
              | left _ => left _
              | right _ => right _
              end
            | String a' s' =>
              match antimirov_prefix e (String a' s') with
              | left _ => left _
              | right _ =>
                match antimirov_substring e s' with
                | left _ => left _
                | right _ => right _
                end
              end
            end) ; clear antimirov_substring.
  +
    apply MkSubstring with (xs := "")(ys := "")(zs := "") ; auto.
  +
    intro contra ; inverts* contra.
    apply empty_string_concat in H0.
    destruct H0.
    symmetry in H1.
    apply empty_string_concat in H1.
    destruct H1 ; substs ; contradiction.
  +
    apply prefix_is_substring ; auto.
  +
    inverts* s0.
    apply MkSubstring with (xs := String a' xs)(ys := ys)(zs := zs) ; auto.
  +
    intro contra ; inverts* contra.
    destruct xs ; simpl in *.
    destruct ys ; simpl in *.
    destruct zs ; simpl in *.
    congruence.
    injects H0.
    assert (Hex : prefix e (String a zs)).
    econstructor ; eauto ; reflexivity.
    contradiction.
    injects H0.
    assert (Hex : prefix e (String a (ys ++ zs))).
    econstructor ; eauto ; reflexivity.
    contradiction.
    injects H0.
    assert (Hex : substring e (xs ++ ys ++ zs)).
    apply MkSubstring with (xs := xs)(ys := ys)(zs := zs) ; auto.
    contradiction.
Defined.
    