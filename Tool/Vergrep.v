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

Definition show_result e xs : substring e xs -> IO unit :=
  fun _ => putStrLn xs.

Definition choose (op : options)(e : regex)(xs : string)
  : IO unit :=
  match alg op with
  | Antimirov  =>
    match antimirov_substring e xs with
    | left s => show_result s
    | right _ => ret tt 
    end
  | Brzozowski =>
    match brzozowski_substring e xs with
    | left s => show_result s
    | right _ => ret tt 
    end
  end.

Fixpoint vergrep (opt : options)(e : regex)(xs : list string) : IO unit :=
  match xs with
  | [] => ret tt
  | (f :: fs) =>
    readFile f >>=
      (fun c => mapM_ unit (choose opt e) (lines c)) >>=
      (fun _ => vergrep opt e fs)
  end.

Definition parse_regex_and_run (opt : options) : IO unit :=
  match regexp opt with
  | None => putStrLn usage
  | Some s =>
    match pexp (from_string s) with
    | [] => putStrLn "parser error!"
    | ((e,_) :: _) => vergrep opt e (files opt)
    end
  end.

Definition main : IO unit :=
  get_args >>=
     (fun args =>
        let opt := parse_options args
        in if version opt
           then putStrLn version_info
           else if help opt
                then putStrLn usage
                else parse_regex_and_run opt).
