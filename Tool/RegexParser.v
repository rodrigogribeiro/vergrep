Set Implicit Arguments.

Require Import
        Ascii
        String
        Utils.Bridge.Parsec
        Syntax.Regex.
        

Definition pchar : parser regex :=
  Chr <$> (none_of (from_string "[]()*+"%string)).

Definition patom : parser regex :=
  (fun es => fold_left Cat es Eps) <$> some pchar.

Definition pstar : parser (regex -> regex) :=
  (fun _ => Star) <$> lexeme (symbol "*").

Definition pplus : parser (regex -> regex) :=
  (fun _ e => e @ (Star e)) <$> lexeme (symbol "+").

Definition pbracketschar : parser regex :=
  Chr <$> none_of (from_string "[]^").

Definition pbrackets : parser regex :=
  (fun es => fold_left Choice es Emp) <$> brackets (many pbracketschar).

Definition pkleene : parser (regex -> regex) :=
  pstar <|> succeed (fun x => x).

Definition pfactor : parser regex :=
  pbrackets <|> patom.

Definition pterm : parser regex :=
  ((fun e g => g e) <$> pfactor) <*> (pplus <|> pstar).

Definition pexp : parser regex :=
  (fun es => fold_left Cat es Eps) <$> many ((parens pterm) <|> pterm).
