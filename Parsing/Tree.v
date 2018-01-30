Set Implicit Arguments.

Require Import
        List 
        Ascii
        String
        Syntax.Regex.

Import ListNotations.

Inductive tree : Set :=
| TEps  : tree
| TChr  : ascii -> tree
| TLeft : tree -> tree
| TRight : tree -> tree
| TCat  : tree -> tree -> tree
| TStar : list tree -> tree.

Section TREE_IND.
  Variable P : tree -> Prop.
  Variable Q : list tree -> Prop.

  Hypothesis
    (H : 

Inductive is_tree_of : tree -> regex -> Prop :=
| ITEps : is_tree_of TEps #1
| ITChr : forall c, is_tree_of (TChr c) ($ c)
| ITLeft : forall tl l r, is_tree_of tl l -> is_tree_of (TLeft tl) (l :+: r) 
| ITRight : forall tr l r, is_tree_of tr r -> is_tree_of (TRight tr) (l :+: r) 
| ITCat : forall tl tr l r, is_tree_of tl l ->
                       is_tree_of tr r ->
                       is_tree_of (TCat tl tr) (l @ r)
| ITStar : forall e ts, Forall (fun t => is_tree_of t e) ts ->
                   is_tree_of (TStar ts)  (e ^*).

Hint Constructors is_tree_of.

Fixpoint flat (t : tree) : string :=
  match t with
  | TEps => ""
  | TChr c => String c ""
  | TLeft t => flat t
  | TRight t => flat t
  | TCat t t' => flat t ++ flat t'
  | TStar ts => fold_right (fun t ac => flat t ++ ac) "" ts
  end.

Lemma flat_correct : forall t e, is_tree_of t e -> (flat t) <<- e.
Proof.
  induction 1 ; crush.
  +
    eapply InCat ; eauto.
  +
    
Qed.