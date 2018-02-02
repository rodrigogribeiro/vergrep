Set Implicit Arguments.

Require Import
        List 
        Ascii
        String
        Syntax.Regex
        Utils.Functions.ListUtils.

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
    (HTEps: P TEps)
    (HTChr : forall a, P (TChr a))
    (HTLeft : forall t, P t -> P (TLeft t))
    (HTRight : forall t, P t -> P (TRight t))
    (HTCat : forall t, P t -> forall t', P t' -> P (TCat t t'))
    (H : forall (ts : list tree), Q ts -> P (TStar ts))
    (H0 : Q (@nil tree))
    (H1 : forall (t : tree),
        P t ->
        forall (ts : list tree), Q ts -> Q (t :: ts)).
  
  Fixpoint tree_ind_full (t : tree) : P t :=
    match t as x return P x with
    | TEps       => HTEps
    | TChr a     => HTChr a
    | TLeft t    => HTLeft (tree_ind_full t)
    | TRight t   => HTRight (tree_ind_full t)
    | TCat t t'  => HTCat (tree_ind_full t) (tree_ind_full t') 
    | TStar ts   => 
      H ((fix l_ind (ts' : list tree) : Q ts' :=
            match ts' as x return Q x with
            | [] => H0
            | t' :: ts'' => H1 (tree_ind_full t') (l_ind ts'')
            end) ts)
    end.
End TREE_IND.

Inductive is_tree_of : tree -> regex -> Prop :=
| ITEps : is_tree_of TEps #1
| ITChr : forall c, is_tree_of (TChr c) ($ c)
| ITLeft : forall tl l r, is_tree_of tl l -> is_tree_of (TLeft tl) (l :+: r) 
| ITRight : forall tr l r, is_tree_of tr r -> is_tree_of (TRight tr) (l :+: r) 
| ITCat : forall tl tr l r, is_tree_of tl l ->
                       is_tree_of tr r ->
                       is_tree_of (TCat tl tr) (l @ r)
| ITStarEnd : forall e, is_tree_of (TStar []) (Star e)
| ITStarRec : forall e ts t, is_tree_of t e ->
                        is_tree_of (TStar ts) (Star e) ->
                        is_tree_of (TStar (t :: ts)) (Star e).

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

Lemma str_append_rewind
  : forall s s' a, String a (s ++ s') = (String a s) ++ s'.
Proof.
  induction s ; crush.
Qed.

Lemma flat_correct : forall t e, is_tree_of t e -> (flat t) <<- e.
Proof.
  intros t e H ; induction H ; crush ; eauto.
  destruct (flat t) eqn : Ha ; eauto.
Qed.