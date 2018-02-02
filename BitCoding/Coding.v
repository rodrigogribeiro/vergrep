Set Implicit Arguments.

Require Import
        Ascii
        List
        Relations.Relation_Operators
        Wellfounded.Lexicographic_Product
        Parsing.Tree
        Utils.Notations
        Utils.Functions.StringUtils
        Syntax.Regex.

Import ListNotations.

(** definition of bits *)

Inductive bit: Set := Zero | One.

(** relating bits with parse trees *)

Open Scope list_scope.

Inductive is_code_of : list bit -> regex -> Prop :=
| ICEps : is_code_of [] #1
| ICChr : forall c, is_code_of [] ($ c)
| ICLeft : forall xs l r, is_code_of xs l ->
                     is_code_of (Zero :: xs) (l :+: r)
| ICRight : forall xs l r, is_code_of xs r ->
                      is_code_of (One :: xs) (l :+: r)
| ICCat : forall xs ys zs l r,
    is_code_of xs l ->
    is_code_of ys r ->
    zs = xs ++ ys ->
    is_code_of zs (l @ r)
| ICStarEnd : forall e, is_code_of [ One ] (e ^*)
| ICStarRec
  : forall xs xss e,
    is_code_of xs e ->
    is_code_of xss (e ^*) ->
    is_code_of (Zero :: xs ++ xss) (e ^*).

Hint Constructors is_code_of.

Fixpoint code (t : tree) : list bit :=
  match t with
  | TEps   => []
  | TChr _ => []
  | TLeft tl => Zero :: code tl
  | TRight tr => One :: code tr
  | TCat tl tr => code tl ++ code tr
  | TStar ts => fold_right (fun t ac => Zero :: code t ++ ac) [ One ] ts
  end.

Lemma code_correct
  : forall t e, is_tree_of t e ->
           is_code_of (code t) e.
Proof.
  intros t e H ; induction H ; simpl ; eauto.
Qed.

Section WF_DECODE.
  Definition decode_input := sigT (fun _ : list bit => regex).

  Definition mk_input (bs : list bit)(e : regex) :=
    existT _ bs e.

  Definition get_bits (inp : decode_input) : list bit :=
    let (bs,_) := inp in bs.

  Definition get_regex (inp : decode_input) : regex :=
    let (_,e) := inp in e.

  Definition decode_input_lt : decode_input -> decode_input -> Prop :=
    lexprod (list bit)
            (fun _ => regex)
            (fun (xs ys : list bit) => List.length xs < List.length ys)
            (fun (xs : list bit)(e e' : regex) => size e < size e').

  Definition wf_decode_input : well_founded decode_input_lt :=
    @wf_lexprod (list bit)
                (fun _ : list bit => regex)
                (fun (xs ys : list bit) => List.length xs < List.length ys)
                (fun (xs : list bit)(e e' : regex) => size e < size e')
                (well_founded_ltof (list bit) (@List.length bit))
                (fun _ => well_founded_ltof regex size).
End WF_DECODE.


Definition decode_type (inp : decode_input) :=
  {p : (tree * list bit) | exists bs1 bs2 t, p = (t,bs1) /\
                                        is_tree_of t (get_regex inp) /\
                                        is_code_of bs1 (get_regex inp) /\
                                        (get_bits inp) = bs1 ++ bs2} +
  {forall t, ~ is_tree_of t (get_regex inp)}.

Definition decode'_body
           (inp : decode_input)
           (decode'
              : forall (inp' : decode_input),
               decode_input_lt inp' inp -> decode_type inp')
  : decode_type inp.
  unfold decode_type.
  destruct inp as [bs e]. simpl in *.
  refine ( match bs, e with
           | _ , #0 => !!
           | _ , #1 => [|| (TEps , bs) ||] 
           | _ , ($ c) => [|| (TChr c, bs) ||]
           | Zero :: bs' , (e :+: e') =>
             match decode' (mk_input bs' e) _ with
             | [|| (tl , bs1) ||] => [|| (TLeft tl, bs1) ||]
             | !! => !!
             end
           | One :: bs' , (e :+: e') =>
             match decode' (mk_input bs' e') _ with
             | [|| (tr , bs1) ||] => [|| (TRight tr, bs1) ||]
             | !! => !!
             end
           | _ , e @ e' =>
             match decode' (mk_input bs e) _ with
             | [|| (tl, bs') ||] =>
               match decode' (mk_input bs' e') _ with
               | [|| (tr, bs'') ||] => [|| (TCat tl tr, bs'') ||]
               | !! => !!
               end
             | !! => !!
             end
           | Zero :: bs' , (Star e) =>
             match decode' (mk_input bs' e) _ with
             | [|| (tl , bs'') ||] =>
               match decode' (mk_input bs'' (Star e)) _ with
               | [|| ((TStar tls), bs''') ||] => [|| (TStar (tl :: tls), bs''') ||]
               | _ => !! 
               end
             | !! => !!
             end
           | One :: bs' , (Star e) => _
           | _ , _ => !!
           end) ; subst* ; simpl in * ; try solve [intros t H ; inverts H].
  Focus 4.

  Require Import Program.

Program Fixpoint decode'
        (inp : decode_input)
        {wf decode_input inp} : option (tree * list bit) :=
  match inp with
  | existT _ bs e => 
    match bs, e with
    | _ , #1 => Some (TEps, bs)
    | _ , ($ a) => Some (TChr a, bs)
    | Zero :: bs', e :+: e' =>
      match decode' (existT bs' e) with
      | Some (tl,bs'') => Some (TLeft tl, bs'')
      | None => None
      end
    | One :: bs', e :+: e' =>
      match decode' (existT bs' e') with
      | Some (tr, bs'') => Some (TRight tr, bs'')
      | None => None
      end
    | _ , e @ e' =>
      match decode' (existT bs e) with
      | Some (tl, bs') =>
        match decode' (existT bs' e') with
        | Some (tr, bs'') => Some (TCat tl tr, bs'')
        | None => None
        end
      | None => None
      end
    | (One :: bs'), (Star e) => Some (TStar [], bs')
    | (Zero :: bs'), (Star e) =>
      match decode' (existT bs' e) with
      | Some (tl, bs1) =>
        match decode' (existT bs1 (Star e)) with
        | Some ((TStar tls), bs2) => Some (TStar (tl :: tls), bs2)
        | _ => None
        end
      | None => None
      end
    | _ , _ => None
    end
  end.
Next Obligation.

(*
Fixpoint decode' (n : nat)(bs : list bit)(e : regex) : option (tree * list bit) :=
  match n with
  | O =>
    match bs, e with
    | [] , #1 => Some (TEps, [])
    | [] , $ a => Some (TChr a, [])
    | [] , _ ^* => Some (TStar [] , [])
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
        match decode' n' bs'' (Star e) with
        | Some (TStar te', bs''') => Some (TStar (te :: te'), bs''')
        | _ => None
        end
      | _ => None
      end
    | One :: bs', Star e => Some (TStar [] , bs') 
    | _ , _  => None
    end
  end.

Lemma decode'_code
  : forall t e, is_tree_of t e ->
           exists bs, decode' (List.length (code t)) (code t) e = Some (t,bs).
Proof.
  intros t e H ; induction H.
  +
    exists (@nil bit) ; crush.
  +
    exists (@nil bit) ; crush.
  +
    destruct IHis_tree_of as [bs Heq].
    exists bs ; crush.
  +
    destruct IHis_tree_of as [bs Heq].
    exists bs ; crush.
  +
    destruct IHis_tree_of1 as [bs Heq].
    destruct IHis_tree_of2 as [bs1 Heq1].
    exists (bs ++ bs1) ; crush.

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
Admitted. *)