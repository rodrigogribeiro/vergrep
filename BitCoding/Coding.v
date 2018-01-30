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

Inductive is_code_of : list bit -> tree -> regex -> Prop :=
| ICEps : is_code_of [] TEps #1
| ICChr : forall c, is_code_of [] (TChr c) ($ c)
| ICLeft : forall xs l r tl, is_code_of xs tl l ->
                        is_code_of (Zero :: xs) (TLeft tl) (l :+: r)
| ICRight : forall xs l r tr, is_code_of xs tr r ->
                         is_code_of (One :: xs) (TRight tr) (l :+: r)
| ICCat : forall xs ys zs l r tl tr,
    is_code_of xs tl l ->
    is_code_of ys tr r ->
    zs = xs ++ ys ->
    is_code_of zs (TCat tl tr) (l @ r)
| ICStarEnd : forall e, is_code_of [ One ] TStarEnd (e ^*)
| ICStarRec
  : forall xs xss e tl tls,
    is_code_of xs tl e ->
    is_code_of xss tls (e ^*) ->
    is_code_of (Zero :: xs ++ xss) (TStarRec tl tls) (e ^*).

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
           is_code_of (code t) t e.
Proof.
  induction t ; intros r H ; inverts* H ; crush ;
  try solve [lets* J : IHt H1] ;
  lets* J : IHt1 H2.
Qed.

Fixpoint decode' (n : nat)(bs : list bit)(e : regex) : option (tree * list bit) :=
  match n with
  | O =>
    match bs, e with
    | [] , #1 => Some (TEps, [])
    | [] , $ a => Some (TChr a, [])
    | [] , _ ^* => Some (TStarEnd, [])
    | [] , #1 @ #1 => Some (TCat TEps TEps, [])
    | [] , #1 :+: _ => Some (TLeft TEps, [])
    | [] , _ :+: #1 => Some (TRight TEps, [])
    | _ , _ => None
    end
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

Lemma decode'_code
  : forall t e, is_tree_of t e ->
           exists bs, decode' (List.length (code t)) (code t) e = Some (t,bs).
Proof.
  induction t ; intros e H ; inverts* H.
  +
    exists (@nil bit) ; crush.
  +
    exists (@nil bit) ; crush.
  +
    lets J : IHt H1.
    destruct J as [bs Heq].
    exists bs ; crush.
  +
    lets J : IHt H1.
    destruct J as [bs Heq].
    exists bs ; crush.
  +
    lets J : IHt1 H2.
    lets J1 : IHt2 H4.
    destruct J as [bs Heq].
    destruct J1 as [bs1 Heq1].
    exists (bs ++ bs1).
    simpl.
    unfold decode'.

Definition decode (bs : list bit)(e : regex) : option tree :=
  match decode' (List.length bs) bs e with
  | Some (t , []) => Some t
  | _             => None
  end.

Theorem decode_code
  : forall t bs e, is_code_of bs t e ->
              is_tree_of t e ->
               decode (code t) e = Some t.
Proof.
  induction t ; intros bs e H Ht ; inverts* H ; inverts* Ht ; crush.
  +
    lets J : IHt H2 H1.

Lemma decode_cat
  : forall tl tr l r, is_tree_of
