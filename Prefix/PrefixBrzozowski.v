Set Implicit Arguments.

Require Import
        Syntax.Regex
        Derivatives.Brzozowski
        Prefix.Prefix
        Tactics.Tactics.


Definition brzozowski_prefix
  : forall e s, {Prefix e s} + {~ Prefix e s}.
  refine (fix brzozowski_prefix e s : {Prefix e s} + {~ Prefix e s} :=
            match s with
            | EmptyString =>
              match null e with
              | left _ => left _
              | right _ => right _
              end
            | String a s' =>
              match brzozowski_prefix (deriv a e) s' with
              | left _ => left _
              | right _ => right _
              end
            end) ; clear brzozowski_prefix ; crush.
