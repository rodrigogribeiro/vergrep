Set Implicit Arguments.


Require Import
        Ascii
        List
        Parsing.Tree
        Utils.Functions.StringUtils
        Syntax.Regex.

Import ListNotations.

(** definition of bits *)

Inductive bit: Set := Zero | One.

(** relating bits with parse trees *)

Open Scope list_scope.

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

Fixpoint decode' (n : nat)(bs : list bit)(e : regex) : option (tree * list bit) :=
  match n with
  | O => None
  | S n' => 
    match bs, e with
    | _ , #1  => Some (TEps, bs)
    | _ , $ a => Some (TChr a, bs)
    | Zero :: bs' , e :+: e' =>
      match decode' n' bs' e with
      | Some (tl, bs'') => Some (TLeft tl , bs'')
      | _               => None
      end
    | One :: bs' , e :+: e' =>
      match decode' n' bs' e' with
      | Some (tr, bs'') => Some (TRight tr , bs'')
      | _               => None
      end
    | _ , e @ e' =>
      match decode' n' bs e with
      | Some (tl , bs') =>
        match decode' n' bs' e' with
        | Some (tr , bs'') => Some (TCat tl tr, bs'')
        | None => None
        end
      | None => None
      end
    | Zero :: bs', e ^* =>
      match decode' n' bs' e with
      | Some (te , bs'') =>
        match decode' n' bs'' (e ^*) with
        | Some (te', bs''') => Some (TStarRec te te', bs''')
        | None => None
        end
      | _ => None
      end
    | One :: bs', e ^* => Some (TStarEnd , bs') 
    | _ , _  => None
    end
  end.

Definition decode (bs : list bit)(e : regex) : option tree :=
  match decode' (List.length bs) bs e with
  | Some (t , []) => Some t
  | _             => None
  end.

