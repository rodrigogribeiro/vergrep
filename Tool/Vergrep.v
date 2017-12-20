Set Implicit Arguments.

Require Import
        Ascii
        List 
        String
        Syntax.Regex
        Substring.Substring
        Tool.Argument
        Tool.RegexParser
        Utils.Utils.

Import ListNotations.

Open Scope string_scope.

Definition usage : string := 
  "Usage: vergrep [OPTIONS] [REGEXP] [FILELIST]" ++
          "\n\nwhere\nOPTIONS\n-B: parse with Brzozowski derivatives\n" ++
          "-A: parse with Antimirov derivatives\n" ++
          "-v: Show version information" ++
          "-h: help message".

Definition version_info : string :=
  "vergrep - version 0.1".

Definition break_on {A : Type}(pbool : A -> bool) : list A -> list (list A) :=
  uncurry cons :@: fold_right (fun x p => if pbool x then ([] , (fst p) :: (snd p))
                                       else (x :: fst p, snd p)) ([],[]).

Definition is_newline (c : ascii) :=
  sumbool_to_bool (ascii_dec c " ")%char.

Definition lines : string -> list string :=
  map to_string :@: break_on is_newline :@: from_string.
  
Definition choose (op : options)(e : regex)(xs : string)
  : {substring e xs} + {~ substring e xs} :=
  match alg op with
  | Antimirov  => antimirov_substring e xs
  | Brzozowski => brzozowski_substring e xs
  end.


(** main driver for the vergrep tool *)

(*
  showResult : ∀ {xs e} → IsSubstring xs e → IO ⊤
  showResult (Substring ys zs ws _ _)
    = putStrLn ("\nLine:" Str.++ xs' Str.++ " matches: " Str.++ zs')
      where
         xs' = Str.fromList (ys List.++ zs List.++ ws)
         zs' = Str.fromList zs

  result : ∀ {xs e} → Dec (IsSubstring xs e) → IO ⊤
  result (yes pr) = showResult pr
  result (no _)   = return tt

  verigrep : Options → Regex → List String → IO ⊤
  verigrep opt r [] = return tt
  verigrep opt r (f ∷ fs)
    = ♯  IO.readFiniteFile f          >>= λ c → 
         ♯ (♯ (IO.mapM′ (result ∘ choose opt r ∘ Str.toList)
                 $ Colist.fromList (lines c))
            >> (♯ verigrep opt r fs))

  main : _
  main = IO.run $
           ♯ getArgs
           >>= λ args →
              ♯ let opt = parseOptions args in
                  if version opt
                  then putStrLn versionInfo
                  else if help opt
                       then putStrLn usage
                       else case Maybe.map (pExp ∘ toList) (regex opt) of λ{
                                 nothing                 → putStrLn usage
                              ;  (just [])               → putStrLn usage 
                              ;  (just (( e , _) ∷ _))   → verigrep opt e (files opt)
                              }   
                      *)  
