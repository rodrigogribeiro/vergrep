Set Implicit Arguments.

Require Import
        List
        String.

Import ListNotations.

(** options for which algorithm will be used *)

Inductive algorithm : Set :=
| Antimirov : algorithm
| Brzozowski : algorithm.

Record options : Set :=
  MkOptions {
    help    : bool
  ; version : bool
  ; alg     : algorithm
  ; regexp  : option string
  ; files   : list string 
  }.

Definition default_options : options :=
  MkOptions false false Brzozowski None [].

Definition is_none {A : Type}(o : option A) : bool :=
  match o with
  | None => true
  | _    => false
  end.

Definition consopt (opt : options)(s : string) : options :=
  match opt with
  | MkOptions h v a r f =>
    if string_dec s "-B" then MkOptions h v Brzozowski r f else
      if string_dec s "-A" then MkOptions h v Antimirov r f else
        if string_dec s "-v" then MkOptions h true a r f else
          if string_dec s "-h" then MkOptions true v a r f else
            if is_none r then MkOptions h v a (Some s) f else
              MkOptions h v a r (s :: f)
  end.

Definition parse_options (args : list string) : options :=
  let result := fold_left consopt args default_options
  in match result with
     | MkOptions h v a r fs => MkOptions h v a r (rev fs)
     end.
