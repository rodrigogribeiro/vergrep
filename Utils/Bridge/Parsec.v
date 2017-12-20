Set Implicit Arguments.

Require Import
        Ascii
        List
        String.

Import ListNotations.

Fixpoint from_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String a' s' => a' :: (from_string s')
  end.

Fixpoint to_string (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Section PARSEC.

  Definition input := list ascii.

  Definition parser (A : Type) := input -> list (A * input)%type.

  (** postulating the main combinators for parsec *)

  Axiom symbol   : ascii -> parser ascii.
  Axiom sat      : (ascii -> bool) -> parser ascii.
  Axiom succeed  : forall {A : Type}, A -> parser A.
  Axiom failure  : forall {A : Type}, parser A.
  Axiom choice   : forall {A : Type}, parser A -> parser A -> parser A.
  Axiom seq      : forall {A B : Type}, parser (B -> A) -> parser B -> parser A.
  Axiom fapp     : forall {A B : Type}, (B -> A) -> parser B -> parser A.
  Axiom many     : forall {A : Type}, parser A -> parser (list A).
  Axiom some     : forall {A : Type}, parser A -> parser (list A).
  Axiom one_of   : list ascii -> parser ascii.
  Axiom none_of  : list ascii -> parser ascii.
  Axiom spaces   : parser unit.
  Axiom lexeme   : forall {A : Type}, parser A -> parser A.
  Axiom parens   : forall {A : Type}, parser A -> parser A.
  Axiom brackets : forall {A : Type}, parser A -> parser A.
End PARSEC.

Notation "p <|> q"   := (choice p q)  (at level 60, right associativity).
Notation "f <$> p"   := (fapp f p)  (at level 59, right associativity).
Notation "p <*> q"   := (seq p q)      (at level 50, left associativity).
Notation "b <* p"    := ((fun a b => a) <$> b <*> p) (at level 59, right associativity).
Notation "b *> p"    := ((fun a b => b) <$> b <*> p) (at level 59, right associativity).
