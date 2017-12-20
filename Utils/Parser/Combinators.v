Set Implicit Arguments.

Require Import
        Ascii
        EqNat
        List
        String.

Import ListNotations.

Fixpoint fromString (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String a' s' => a' :: fromString s'
  end.


Definition input := list ascii.

Section BASICS.

  Definition parser (A : Type) := input -> list (A * input)%type.

  Definition symbol (c : ascii) : parser ascii :=
    fun s => match s with
          | [] => []
          | (x :: xs) => if ascii_dec x c then [ (c , xs) ] else []
          end.

  Definition succeed {A : Type} (x : A) : parser A :=
    fun s => [ (x , s) ].

  Definition failure {A : Type} : parser A :=
    fun s => [].

  Definition par {A : Type} (l r : parser A) :=
    fun s => l s ++ r s.

  Definition seq {A B : Type}(l : parser (B -> A))(r : parser B) :=
    fun s => flat_map (fun f => map (fun g =>
                                 ( (fst f) (fst g)
                                 , (snd g)))
                                 (r (snd f))) (l s).  

  Definition choice {A : Type}(ps : list (parser A)) :=
    fold_right par failure ps.

  Definition sat (p : ascii -> bool) : parser ascii :=
    fun s => match s with
          | [] => []
          | (x :: xs) => if p x then [ (x , xs) ] else []
          end.

End BASICS.

Notation "p <|> q"   := (par p q)  (at level 60, right associativity).
Notation "f <$> p"   := (seq (succeed f) p)  (at level 59, right associativity).
Notation "p <*> q"   := (seq p q)      (at level 50, left associativity).
Notation "b <* p"    := ((fun a b => a) <$> b <*> p) (at level 59, right associativity).
Notation "b *> p"    := ((fun a b => b) <$> b <*> p) (at level 59, right associativity).

Section MANY.
  Fixpoint many {A : Type}(fuel : nat)(p : parser A) : parser (list A) :=
    match fuel with
    | O => succeed []
    | S n' => ((fun a b => a :: b) <$> p) <*> many n' p
    end.
End MANY.

Section CHARS.

  Definition one_of (cs : list ascii) : parser ascii :=
    sat (fun c => if in_dec ascii_dec c cs then true else false).

  Definition none_of (cs : list ascii) : parser ascii :=
    sat (fun c => if in_dec ascii_dec c cs then false else true).
  
  Definition is_white (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (beq_nat n 32)   (* space *)
           (beq_nat n 9))   (* tab *)
      (orb (beq_nat n 10)   (* linefeed *)
           (beq_nat n 13)). (* Carriage return. *)

  Definition spaces (n : nat) : parser unit :=
    (fun _ => tt) <$> many n (sat is_white).

  Definition lexeme {A : Type} (n : nat)(p : parser A) : parser A :=
    ((fun a b => a) <$> p) <*> spaces n.

  Definition between {A : Type}(l : parser ascii)(p : parser A)(r : parser ascii) :=
    ((fun a b c => b) <$> l) <*> p <*> r.

  Open Scope char_scope.

  Definition brackets {A : Type}(p : parser A) :=
    between (symbol "[") p (symbol "]").

  Definition parens {A : Type}(p : parser A) :=
    between (symbol "(") p (symbol ")").  
End CHARS.
