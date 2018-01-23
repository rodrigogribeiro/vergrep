Set Implicit Arguments.

Require Import
        Ascii
        String
        Syntax.Regex.

Inductive tree : Set :=
| TEps  : tree
| TChr  : ascii -> tree
| TLeft : tree -> tree
| TRight : tree -> tree
| TCat  : tree -> tree -> tree
| TStarEnd : tree 
| TStarRec : tree -> tree -> tree.

Inductive is_tree_of : tree -> regex -> Prop :=
| ITEps : is_tree_of TEps #1
| ITChr : forall c, is_tree_of (TChr c) ($ c)
| ITLeft : forall tl l r, is_tree_of tl l -> is_tree_of (TLeft tl) (l :+: r) 
| ITRight : forall tr l r, is_tree_of tr r -> is_tree_of (TRight tr) (l :+: r) 
| ITCat : forall tl tr l r, is_tree_of tl l ->
                       is_tree_of tr r ->
                       is_tree_of (TCat tl tr) (l @ r)
| ITStarEnd : forall l, is_tree_of TStarEnd (l ^*)
| ITStarRec :
    forall l tl tls, is_tree_of tl l ->
                is_tree_of tls (l ^*) ->
                is_tree_of (TStarRec tl tls) (l ^*).

Hint Constructors is_tree_of.

Fixpoint flat (t : tree) : string :=
  match t with
  | TEps => ""
  | TChr c => String c ""
  | TLeft t => flat t
  | TRight t => flat t
  | TCat t t' => flat t ++ flat t'
  | TStarEnd => ""
  | TStarRec t ts => flat t ++ flat ts
  end.

Lemma flat_correct : forall t e, is_tree_of t e -> (flat t) <<- e.
Proof.
  induction t ; intros e H ; inverts H ; simpl in * ; jauto.
  +
    lets J : IHt1 H2.
    lets K : IHt2 H4.
    destruct (flat t1) eqn : Ha ; simpl in * ; jauto.
Qed.

