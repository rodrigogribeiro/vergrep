module PrefixAntimirov where

import qualified Prelude
import qualified Antimirov
import qualified List
import qualified Regex

antimirov_prefix :: Regex.Coq_regex -> Prelude.String -> Prelude.Bool
antimirov_prefix e s =
  case s of {
   [] -> Regex.null e;
   (:) a' s' ->
    case Regex.null e of {
     Prelude.True -> Prelude.True;
     Prelude.False ->
      List.coq_Exists_dec (Antimirov.pderiv a' e) (\e' ->
        antimirov_prefix e' s')}}

