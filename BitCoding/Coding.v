Set Implicit Arguments.


Require Import
        Ascii
        List
        String
        Parsing.Tree
        Syntax.Regex.

Import ListNotations.

Open Scope list_scope.

(** definition of bits *)

Inductive bit: Set := Zero | One.

(** relating bits with parse trees *)

Inductive is_code_of : list bit -> tree -> Prop :=
| ICEps : is_code_of [] TEps
| ICChr : forall c, is_code_of [] (TChr c)
| ICLeft : forall xs l, is_code_of xs l ->
                   is_code_of (Zero :: xs) (TLeft l)
| ICRight : forall xs r, is_code_of xs r ->
                    is_code_of (One :: xs) (TRight r)
| ICCat : forall xs ys zs l r,
    is_code_of xs l ->
    is_code_of ys r ->
    zs = xs ++ ys ->
    is_code_of zs (TCat l r)
| ICStarEnd : is_code_of [ One ] TStarEnd
| ICStarRec
  : forall xs xss tl tls,
    is_code_of xs tl  ->
    is_code_of xss tls ->
    is_code_of (Zero :: xs ++ xss) (TStarRec tl tls).

Hint Constructors is_code_of.

Fixpoint code (t : tree) : list bit :=
  match t with
  | TEps   => []
  | TChr _ => []
  | TLeft tl => Zero :: code tl
  | TRight tr => One :: code tr
  | TCat tl tr => code tl ++ code tr
  | TStarEnd => [ One ]
  | TStarRec tl tls => Zero :: code tl ++ code tls
  end.

Lemma code_correct
  : forall t e, is_tree_of t e ->
           is_code_of (code t) t.
Proof.
  induction t ; intros r H ; inverts* H ; crush ;
  try solve [lets* J : IHt H1] ;
  lets* J : IHt1 H2.
Qed.