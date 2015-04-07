(** 

-----------Foraml proof for AVL properties-----------
CS 6301.006 Final Project Assignment
Team: Rabimba Karanjai 
Instructor: Dr. Kevin Hamlen 
Department of Computer Science 
University of Texas at Dallas 

**)




(*Require Export Basics.*)

(** This file contains useful definitions and functions used in the
    rest of the project.
**)

(* ##################################################### *)
(** ** Cases *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
Tactic Notation "SSSSSSSSCase" constr(name) := Case_aux SSSSSSSSCase name.

(* ##################################################### *)
(** ** Natural numbers *)

(** The beq_nat function tests natural numbers for equality,
    yielding a boolean.
**)
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O    => match m with
            | O    => true
            | S m' => false
            end
  | S n' => match m with
            | O    => false
            | S m' => beq_nat n' m'
            end
  end.

(** The ble_nat function tests natural numbers for less-or-equal,
    yielding a boolean.
**)
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O    => true
  | S n' => match m with
            | O    => false
            | S m' => ble_nat n' m'
            end
  end.

(** The blt_nat function tests natural numbers for less-than,
    yielding a boolean.
**)
Definition blt_nat (n m : nat) : bool :=
  match ble_nat n m with
  | false => false
  | true  => negb (beq_nat n m)
  end.

(** The three cases yielded by the compare function:
    - Lt: less than
    - Eq: equals
    - Gt: greater than
**)
Inductive compopt : Type :=
  | Lt : compopt
  | Eq : compopt
  | Gt : compopt.

(** The compare function compares two natural numbers and yields
    a compopt.
**)
Definition compare (n m : nat) : compopt :=
  match beq_nat n m with
  | true  => Eq
  | false => match blt_nat n m with
             | true  => Lt
             | false => Gt
             end
  end.

(* The maximum between two natural numbers. *)
Definition max (n : nat) (m : nat) : nat :=
  match ble_nat n m with
  | true  => m
  | false => n
  end.

(* The less than or equals proposition. *)
Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(* The "strictly less than" relation n < m. *)
Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(* ##################################################### *)
(** ** Lists *)

(* The list structure, with natural numbers. *)
Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(* The append function. *)
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

(** A "cons on the right" function "snoc". *)
Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

(* The head of the list. *)
Definition head (l : natlist) : nat :=
  match l with
  | nil    => 0
  | h :: t => h
  end.

(* The last element of the list. *)
Fixpoint last (l : natlist) : nat :=
  match l with
  | nil    => 0
  | [x]    => x
  | _ :: t => last t
  end.

(* ##################################################### *)
(* The AVL tree structure *)
Inductive avltree : Type :=
 | leaf : avltree
 | node : avltree -> nat -> avltree -> avltree.

Check avltree_ind.

(* ##################################################### *)
(** ** Functions for Binary Search Trees (BST) *)

(* An add function for binary search trees only *)
Fixpoint add_bst (n : nat) (t : avltree) : avltree :=
  match t with
  | leaf       => node leaf n leaf
  | node l v r => match ble_nat n v with
                      | true  => node (add_bst n l) v r
                      | false => node l v (add_bst n r)
                      end
  end.

Fixpoint lower_right (t : avltree) : nat :=
  match t with
  | leaf          => O
  | node leaf v r => v
  | node l v r    => lower_right l
  end.


(* The delete function for binary search trees only *)
Fixpoint delete_bst (n : nat) (t : avltree) : avltree :=
  match t with
  | leaf       => leaf
  | node l v r => match beq_nat n v with
                      | true  => match t with
                             | leaf             => leaf
                             | node leaf v leaf => leaf
                             | node leaf v r    => r
                             | node l v leaf    => l
                             | node l v r       => node l (lower_right r) (delete_bst (lower_right r) r)
                             end
                      | false => match ble_nat n v with
                                 | true  => node (delete_bst n l) v r
                                 | false => node l v (delete_bst n r)
                                 end
                      end
  end.

(* If a natural number is present in the tree or not. *)
Fixpoint tree_member (n : nat) (t : avltree) : bool :=
  match t with
  | leaf       => false
  | node l v r => match beq_nat n v with
                     | true  => true
                     | false => orb (tree_member n l) (tree_member n r)
                     end
  end.

(* Returns the left-subtree of the tree t. *)
Definition left (t : avltree) : avltree :=
  match t with
  | leaf       => leaf
  | node l _ _ => l
  end.

(* Returns the value of the node t. *)
Definition value (t : avltree) : nat :=
  match t with
  | leaf       => 0
  | node _ v _ => v
  end.

(* Returns the right-subtree of the tree t. *)
Definition right (t : avltree) : avltree :=
  match t with
  | leaf       => leaf
  | node _ _ r => r
  end.

(* ##################################################### *)
(** ** Height-related functions and balancing *)

(** The height of a tree is the length of the longest downward path
    to a leaf from the root node.
    Leaf nodes have height zero, and a tree with only a single node
    has height one.
**)
Fixpoint height (t : avltree) : nat :=
  match t with
  | leaf       => 0
  | node l v r => 1 + (max (height l) (height r))
  end.

(** The 'heightoption' avoids the use of negative numbers. It gives us
    which subtree outweighs the other, by which factor.
    - Balanced : the balance factor is zero, meaning the tree is balanced.
    - Leftopt : the balance factor is positive, meaning the left subtree
                outweighs the right subtree.
    - Rightopt : the balance factor is negative, meaning the right subtree
                outweighs the left subtree.
**)
Inductive heightoption : Type :=
  | Balanced : heightoption
  | Leftopt  : nat -> heightoption
  | Rightopt : nat -> heightoption.

(** The balance factor is calculated as follows:
    balanceFactor = height(left-subtree) - height(right-subtree)

    If the balance factor is -2, it returns Rightopt 2.
    If the balance factor is -1, it returns Rightopt 1.
    If the balance factor is  0, it returns Balanced.
    If the balance factor is +1, it returns Leftopt 1.
    If the balance factor is +2, it returns Leftopt 2.
**)
Definition balanceFactor (t : avltree) : heightoption :=
  match t with
  | leaf       => Balanced
  | node l v r => match compare (height l) (height r) with
                  | Lt => Rightopt ((height r) - (height l))
                  | Eq => Balanced
                  | Gt => Leftopt ((height l) - (height r))
                  end
  end.

(** This is a proposition using the heightoption type.
    This says a tree has a height balanced if we have any of these
    proposition after the computation of 'balanceFactor':
    Leftopt 1, Balanced, Rightopt 1.

    It is used in the 'balanced' proposition.
**)
Inductive heightbalanced : heightoption -> Prop :=
  hb       : heightbalanced (Balanced)
| hb_left  : forall n, n <= 1 -> heightbalanced (Leftopt n)
| hb_right : forall n, n <= 1 -> heightbalanced (Rightopt n).

(** This proposition says if a tree is balanced or not.
    A leaf is balanced.
    A single node is balanced.
    A tree is balanced if the absolute value of the balance factor is
    less than or equals to 1, its left-subtree is balanced, and its
    right-subtree is balanced
**)
Inductive balanced : avltree -> Prop :=
  b_leaf : balanced leaf
| b_one  : forall v, balanced (node leaf v leaf) 
| b_rec  : forall l v r, heightbalanced (balanceFactor (node l v r))
                        -> balanced l -> balanced r -> balanced (node l v r).

(* ##################################################### *)
(** ** List-related functions *)

(* The inorder walk in an AVL tree, returning a list of all the elements. *)
Fixpoint inorder (t : avltree) : natlist :=
  match t with
  | leaf       => nil
  | node l v r => (inorder l) ++  [v]  ++ (inorder r)
  end.

(* The proposition saying if the elements of a list are sorted. *)
Inductive sorted : natlist -> Prop :=
  s_nil : sorted nil
| s_one : forall h, sorted [h]
| s_rec : forall h1 h2 t, h1 <= h2 -> sorted (h2::t) -> sorted (h1::h2::t).

(* ##################################################### *)
(** ** Rotation functions *)

(* The right rotation operation on a binary tree. *)
Fixpoint rightrotation (t : avltree) : avltree :=
  match t with
  | leaf                       => leaf
  | node leaf v r              => t
  | node (node l2 v2 r2) v1 r1 => node l2 v2 (node r2 v1 r1)
  end.

(* The left rotation operation on a binary tree. *)
Fixpoint leftrotation (t : avltree) : avltree :=
  match t with
  | leaf                       => leaf
  | node l v leaf              => t
  | node l1 v1 (node l2 v2 r2) => node (node l1 v1 l2) v2 r2
  end.

(** The balancing function balances a tree with rotations.
    If the tree is already balanced, or the balance factor is +1
    or -1, we don't change the tree.
    There are four cases when we need to rotate the tree:
    - If the balance factor of the root node is -2, and the balance
      factor of its right subtree is -1, then a single left rotation
      is needed.
    - If the balance factor of the root node is -2, and the balance
      factor of its right subtree is +1, two rotations are needed:
      first a right rotation on the right subtree and then a left
      rotation on the root node.
    - If the balance factor of the root node is +2, and the balance
      factor of its left subtree is +1, then a single right rotation
      is needed.
    - If the balance factor of the root node is +2, and the balance
      factor of its left subtree is -1, two rotations are needed:
      first a left rotation on the left subtree and then a right
      rotation on the root node.
**)
Definition balancing (t : avltree) : avltree :=
  match balanceFactor t with
  | Balanced   => t
  | Rightopt 1 => t
  | Rightopt _ => match balanceFactor (right t) with
                  | Balanced   => leftrotation t
                  | Rightopt _ => leftrotation t
                  | Leftopt _  => leftrotation (node (left t) (value t) (rightrotation (right t)))
                  end
  | Leftopt 1  => t
  | Leftopt _  => match balanceFactor (left t) with
                  | Balanced   => rightrotation t
                  | Leftopt _  => rightrotation t
                  | Rightopt _ => rightrotation (node (leftrotation (left t)) (value t) (right t))
                  end
  end.

(** The add function of an AVL tree, allowing the insertion of a new node,
    and rebalancing the AVL tree if it's not balanced anymore.
    If the node already exists in the tree, it is not added.
**)
Fixpoint add (n : nat) (t : avltree) : avltree :=
  match t with
  | leaf       => node leaf n leaf
  | node l v r => match compare n v with
                      | Lt => balancing (node (add n l) v r)
                  | Eq => t
                      | Gt => balancing (node l v (add n r))
                      end
  end.

(* ##################################################### *)
Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = O".
    apply le_n.
  Case "n = S n'".
    apply le_S. apply IHn'.
Qed.

Lemma app_com : forall l1 n l2,
  l1 ++ n :: l2 = (snoc l1 n) ++ l2.
Proof.
  intros.
  induction l1.
  Case "l1 = []".
    simpl. reflexivity.
  Case "l1 = n0 :: l1".
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma app_nil : forall l1 l2,
  l1 ++ l2 = [] ->  l2 = [].
Proof.
  intros.
  induction l1.
  Case "l1 = []".
    simpl in H.
    apply H.
  Case "l1 = n :: l1".
    inversion H.
Qed.

Lemma last_app' l1 l2 (H : l1 <> []) :
  last (l2 ++ l1) = last l1.
Proof.
  induction l2.
  Case "l2 = []".
    simpl. reflexivity.

  Case "l2 = n :: l2".
    assert (last ((n :: l2) ++ l1) = last (l2 ++ l1)).
    SCase "Proof of assertion".
      simpl.
      remember (l2 ++ l1) as l; destruct l.
      SSCase "l2 ++ l1 = []".
        symmetry in Heql.
        apply app_nil in Heql.
        apply H in Heql.
        inversion Heql.
      SSCase "l2 ++ l1 = n0 :: l".
        reflexivity.

    rewrite H0.
    apply IHl2.
Qed.

Lemma last_cons' n0 l1 (H : l1 <> []) :
  last (n0 :: l1) = last l1.
Proof.
  assert (n0 :: l1 = [n0] ++ l1).
  Case "Proof of assertion".
    simpl. reflexivity.

  rewrite H0.
  apply last_app'.
  apply H.
Qed.

Lemma tree_in_list : forall n t1 t2,
  sorted (inorder (node t1 n t2)) = sorted ((inorder t1) ++ n :: (inorder t2)).
Proof.
  intros.
  auto.
Qed.

Lemma sorted_cons : forall n l,
  sorted (n :: l) -> sorted l.
Proof.
  intros.
  inversion H.
  apply s_nil.
  apply H3.
Qed.

Lemma sorted_first : forall l1 l2,
  sorted (l1 ++ l2) -> sorted l1.
Proof.
  intros.
  induction l1.
  Case "l1 = []".
    apply s_nil.
  Case "l1 = n :: l1".
    destruct l1.
    SCase "l1 = []".
      apply s_one.
    SCase "l1 = n0 :: l1".
      apply s_rec.
      inversion H.
      apply H2.
      inversion H.
      apply IHl1.
      apply H4.
Qed.

Lemma sorted_app_simpl : forall l1 l2,
  sorted(l1++l2) -> sorted l1 /\ sorted l2.
Proof.
  intros.
  split.
  Case "left".
    apply sorted_first in H.
    apply H.
  Case "right".
    induction l1.
    SCase "l1 = []".
      simpl in H.
      apply H.

    SCase "l1 = n :: l1".
      simpl in H.
      apply sorted_cons in H.
      apply IHl1 in H.
      apply H.
Qed.

Lemma sorted_app2 xs ys (Hxs : sorted xs) (Hys : sorted ys) 
  (H: last xs <= head ys) : sorted (xs ++ ys).
Proof.
  induction Hxs; simpl in *; [assumption | |].
  destruct ys; simpl in *; [apply s_one | apply s_rec; assumption].
  apply s_rec; [assumption| apply IHHxs; assumption].
Qed.

Lemma sorted_head l (H : l <> []) : forall n,
  sorted (n :: l) -> n <= head l.
Proof.
  intros.
  inversion H0.
  unfold not in H.
  symmetry in H3.
  apply H in H3.
  inversion H3.
  simpl.
  auto.
Qed.

Lemma O_sorted : forall l,
  sorted l -> sorted (0 :: l).
Proof.
  intros.
  inversion H.
  apply s_one.
  apply s_rec.
  apply O_le_n.
  apply s_one.
  apply s_rec.
  apply O_le_n.
  rewrite H2.
  auto.
Qed.

Lemma last_cons'' : forall n l,
  last (n :: l) = last l \/ (l = [] /\ last (n :: l) = n).
Proof.
  intros.
  induction l.
  Case "l = []".
    right.
    auto.
  Case "l = n0 :: l".
    left.
    apply last_cons'.
    unfold not.
    intros.
    inversion H.
Qed. 

Lemma sorted_last : forall l1 l2,
  sorted (l1 ++ l2) -> sorted (last l1 :: l2) \/ l2 = [].
Proof.
  intros.
  induction l1.
  Case "l1 = []".
    simpl in *.
    left.
    apply O_sorted.
    auto.
  Case "l1 = n :: l1".
    simpl in H.
    inversion H.
    symmetry in H2.
    apply app_nil in H2.
    auto.

    assert (last (n :: l1) = last l1 \/ (l1 = [] /\ last (n :: l1) = n)).
      apply last_cons''.

    inversion H4.
    rewrite H5.
    rewrite H1 in H3.
    apply IHl1 in H3.
    apply H3.
    inversion H5.
    rewrite H7.
    rewrite H6 in H.
    simpl in H.
    auto.
Qed.

Lemma sorted_app' : forall l1 l2,
  sorted(l1++l2) -> sorted l1 /\ sorted l2 /\ (last l1 <= head l2 \/ l2 = []).
Proof.
  intros.
  split.
  Case "sorted l1".
    apply sorted_first in H.
    auto.
  split.
  Case "sorted l2".
    apply sorted_app_simpl in H.
    inversion H.
    auto.
  Case "last l1 <= head l2 \/ l2 = []".
    apply sorted_last in H.
    inversion H.
    inversion H0.
    auto.
    simpl.
    auto.
    auto.
Qed.

Lemma inorder_node : forall l v r,
  inorder (node l v r) <> [].
Proof.
  unfold not.
  intros.
  inversion H.
  apply app_nil in H1.
  inversion H1.
Qed.

Lemma sorted_cons' : forall n t,
  sorted (n :: inorder t) <->
  (n <= head (inorder t) \/ t = leaf) /\ sorted (inorder t).
Proof.
  intros.
  split.
  Case "Left part of the equivalence".
    intros.

    assert (n :: inorder t = [n] ++ inorder t).
    SCase "Proof of assertion".
      simpl. reflexivity.

    rewrite H0 in H.
    apply sorted_app' in H.
    inversion H.
    inversion H2.
    split.
    SCase "n <= head (inorder t) \/ t = leaf".
      simpl in *.
      assert (inorder t = [] -> t = leaf).
      SSCase "Proof of assertion".
        intros.
        destruct t.
        SSSCase "t = leaf".
          reflexivity.
        SSSCase "t = node t1 n0 t2".
          apply inorder_node in H5.
          inversion H5.
      
      inversion H4.
      left.
      apply H6.
      apply H5 in H6.
      right.
      apply H6.
    SCase "sorted (inorder t)".
      apply H3.

  Case "Right part of the equivalence".
    intros.
    inversion H.
    inversion H0.
    clear H.

    assert (n :: inorder t = [n] ++ inorder t).
    SCase "Proof of assertion".
      simpl. reflexivity.

    rewrite H.
    apply sorted_app2.
    apply s_one.
    apply H1.
    simpl in *.
    apply H2.
    subst.
    simpl.
    apply s_one.
Qed.

Lemma sorted_cons''' : forall n l,
  sorted (n :: l) <->
  (n <= head l \/ l = []) /\ sorted l.
Proof.
  intros.
  split.
  Case "Left part of the equivalence".
    intros.

    assert (n :: l = [n] ++ l).
    SCase "Proof of assertion".
      simpl. reflexivity.

    rewrite H0 in H.
    apply sorted_app' in H.
    inversion H.
    inversion H2.
    split.
    SCase "n <= head (inorder t) \/ t = leaf".
      simpl in *.
      inversion H4.
      left. apply H5.
      right. apply H5.
    SCase "sorted (inorder t)".
      apply H3.

  Case "Right part of the equivalence".
    intros.
    inversion H.
    inversion H0.
    clear H.

    assert (n :: l = [n] ++ l).
    SCase "Proof of assertion".
      simpl. reflexivity.

    rewrite H.
    apply sorted_app2.
    apply s_one.
    apply H1.
    simpl in *.
    apply H2.
    subst.
    simpl.
    apply s_one.
Qed.

Lemma sorted_app'' (l2 : natlist) (Hl2 : l2 <> []) : forall l1,
  sorted(l1++l2) -> sorted l1 /\ sorted l2 /\ last l1 <= head l2.
Proof.
  intros.
  split.
  Case "sorted l1".
    apply sorted_first in H.
    apply H.

  split.
  Case "sorted l2".
    apply sorted_app_simpl in H.
    inversion H.
    apply H1.

  Case "last l1 <= head l2".
    induction l1.
    SCase "l1 = []".
      simpl.
      apply O_le_n.
    SCase "l1 = n :: l1".
      simpl in H.
      assert (sorted (n :: l1 ++ l2)).
        apply H.

      apply sorted_cons in H.
      apply IHl1 in H.

      destruct l2.
      SSCase "l2 = []".
        unfold not in Hl2.
        assert ([] = []).
          reflexivity.
        apply Hl2 in H1.
        inversion H1.
      SSCase "l2 = n0 :: l2".
        apply sorted_app' with (l1:=n :: l1) in H0.
        inversion H0.
        inversion H2.
        inversion H4.
        auto.
        inversion H5.
Qed.

Lemma list_assoc : forall t1 t2 t3,
  (t1++t2)++t3 = t1++t2++t3.
Proof.
  intros.
  induction t1.
  Case "t1 = []".
    simpl. reflexivity.
  Case "t1 = n :: t1".
    simpl.
    rewrite IHt1.
    reflexivity.
Qed.

Lemma if_eq_true (P Q : bool) : 
  true = (if P then Q else false) -> P = true.
Proof.
  intros.
  destruct P.
  Case "P = true".
    reflexivity.
  Case "P = false".
    inversion H.
Qed.

Lemma blt_imp_ble : forall e n,
  true = blt_nat e n -> true = ble_nat e n.
Proof.
  intros.
  unfold blt_nat in H.
  apply if_eq_true in H.
  symmetry. apply H.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  apply le_n.
  apply le_S.
  apply IHle.
Qed.

Lemma ble_imp_le : forall n m,
  true = ble_nat n m -> n <= m.
Proof.
  induction n; intros.
  Case "n = 0".
    induction m.
    SCase "m = 0".
      apply le_n.
    SCase "m = S m".
      apply le_S.
      apply IHm.
      auto.
  Case "n = S n".
    destruct m.
    SCase "m = 0".
      inversion H.
    SCase "m = S m".
      apply n_le_m__Sn_le_Sm.
      apply IHn.
      inversion H.
      auto.
Qed.

Lemma inorder_rightrotation : forall t,
  inorder t = inorder (rightrotation t).
Proof.
  intros.
  induction t.
  Case "t = leaf".
    auto.
  Case "t = node t1 n t2".
    simpl.
    destruct t1.
    SCase "t1 = leaf".
      auto.
    SCase "t1 = node t1_1 n0 t1_2".
      simpl.
      rewrite list_assoc.
      reflexivity. 
Qed.

Lemma inorder_leftrotation : forall t,
  inorder t = inorder (leftrotation t).
Proof.
  intros.
  induction t.
  Case "t = leaf".
    auto.
  Case "t = node t1 n t2".
    simpl.
    destruct t2.
    SCase "t2 = leaf".
      auto.
    SCase "t2 = node t2_1 n0 t2_2".
      simpl.
      rewrite list_assoc.
      reflexivity. 
Qed.

Lemma inorder_balancing : forall t,
  inorder t = inorder (balancing t).
Proof.
  intros.
  induction t.
  Case "t = leaf".
    auto.
  Case "t = node t1 n t2".
    unfold balancing.
    destruct balanceFactor.
    SCase "Balanced".
      reflexivity.
    SCase "Leftopt".
      destruct n0.
      SSCase "n0 = O".
        destruct balanceFactor;
        rewrite inorder_rightrotation;
        auto.
        SSSCase "Rightopt".
          simpl.
          remember t1 as x; destruct x.
          SSSSCase "t1 = leaf".
            auto.
          SSSSCase "t1 = node x1 n1 x2 ".
            simpl.
            destruct x2.
            SSSSSCase "x2 = leaf".
              auto.
            SSSSSCase "x2 = node x2_1 n2 x2_2".
              simpl. rewrite list_assoc.
              simpl. rewrite list_assoc.
              auto.
       destruct n0.
       SSCase "n0 = 1".
         auto.
       SSCase "n0 = S S _".
         destruct balanceFactor;
         rewrite inorder_rightrotation;
         auto.
         SSSCase "Rightopt".
           simpl.
           remember t1 as x; destruct x.
           SSSSCase "t1 = leaf".
             auto.
           SSSSCase "t1 = node x1 n1 x2 ".
             simpl.
             destruct x2.
             SSSSSCase "x2 = leaf".
               auto.
             SSSSSCase "x2 = node x2_1 n2 x2_2".
               simpl. rewrite list_assoc.
               simpl. rewrite list_assoc.
               auto.
    SCase "Rightopt".
      destruct n0.
      SSCase "n0 = O".
        destruct balanceFactor;
        rewrite inorder_leftrotation;
        auto.
        SSSCase "Leftopt".
          simpl.
          remember t2 as x; destruct x.
          SSSSCase "t2 = leaf".
            auto.
          SSSSCase "t2 = node x1 n1 x2 ".
            simpl.
            destruct x1.
            SSSSSCase "x1 = leaf".
              auto.
            SSSSSCase "x1 = node x1_1 n2 x1_2".
              simpl. rewrite list_assoc.
              simpl. rewrite list_assoc.
              rewrite list_assoc.
              auto.
       destruct n0.
       SSCase "n0 = 1".
         auto.
       SSCase "n0 = S S _".
         destruct balanceFactor;
         rewrite inorder_leftrotation;
         auto.
         SSSCase "Leftopt".
           simpl.
           remember t2 as x; destruct x.
           SSSSCase "t2 = leaf".
             auto.
           SSSSCase "t2 = node x1 n2 x2 ".
             simpl.
             destruct x1.
             SSSSSCase "x1 = leaf".
               auto.
             SSSSSCase "x1 = node x1_1 n2 x1_2".
               simpl. rewrite list_assoc.
               simpl. repeat rewrite list_assoc.
               auto.
Qed.

Lemma last_balancing : forall t,
  last (inorder (balancing t)) = last (inorder t).
Proof.
  intros.
  rewrite <- inorder_balancing.
  auto.
Qed.

Lemma inorder_add_node : forall t e,
  inorder (add e t) <> [].
Proof.
  intros.
  induction t.
  Case "t = leaf".
    simpl.
    simpl. unfold not. intro. inversion H.
  Case "t = node t1 n t2".
    simpl.
    destruct compare.
    SCase "compare e n = Lt".
      rewrite <- inorder_balancing.
      simpl.
      simpl; unfold not; intro; apply app_nil in H; inversion H.
    SCase "compare e n = Eq".
      simpl; unfold not; intro; apply app_nil in H; inversion H.
    SCase "compare e n = Gt".
      rewrite <- inorder_balancing.
      simpl; unfold not; intro; apply app_nil in H; inversion H.
Qed.

Lemma last_add : forall e n t,
  true = blt_nat e n -> 
  last (inorder t) <= n ->
  last (inorder (add e t)) <= n.
Proof.
  intros.
  induction t.
  Case "t = leaf".
    simpl.
    apply blt_imp_ble in H.
    apply ble_imp_le in H.
    apply H.
  Case "t = node t1 n0 t2".
    simpl in H0.
    simpl.
    destruct compare.
    SCase "compare e n0 = Lt".
      rewrite last_balancing.
      simpl.
      rewrite last_app'.
      rewrite last_app' in H0.
      apply H0.
      unfold not. intro. inversion H1.
      unfold not. intro. inversion H1.
    SCase "compare e n0 = Eq".
      simpl.
      apply H0.
    SCase "compare e n0 = Gt".
      rewrite last_balancing.
      simpl.
      rewrite last_app'.
      rewrite last_app' in H0.
      remember t2 as x; destruct x.
      SSCase "t2 = leaf".
        simpl in *.

        assert (0 <= n).
        SSSCase "Proof of assertion".
          apply O_le_n.

        apply IHt2 in H1.
        apply H1.
      SSCase "t2 = node x1 n1 x2".
        rewrite last_cons' in H0.
        apply IHt2 in H0.
        rewrite last_cons'.
        apply H0.
        apply inorder_add_node.
        apply inorder_node.
        unfold not. intro. inversion H1.
        unfold not. intro. inversion H1.
Qed.

Lemma rightrotation_sorted : forall t,
  sorted (inorder t) -> sorted (inorder (rightrotation t)).
Proof.
  intros.
  induction t.
  Case "t = leaf".
    simpl. apply s_nil.
  Case "t = node t1 n t2".
    simpl.
    destruct t1.
    SCase "t1 = leaf".
      apply H.
    SCase "t1 = node t1_1 n0 t1_2".
      simpl in *. 
      rewrite list_assoc in H.
      simpl in H.
      apply H.
Qed.

Lemma leftrotation_sorted : forall t,
  sorted (inorder t) -> sorted (inorder (leftrotation t)).
Proof.
  intros.
  induction t.
  Case "t = leaf".
    simpl. apply s_nil.
  Case "t = node t1 n t2".
    simpl.
    destruct t2.
    SCase "t2 = leaf".
      apply H.
    SCase "t2 = node t2_1 n0 t2_2".
      simpl in *. 
      rewrite list_assoc.
      apply H.
Qed.

Lemma blt_S: forall b e n,
  b = blt_nat (S e) (S n) -> b = blt_nat e n.
Proof.
  auto.
Qed.

Lemma le_imp_le_S : forall e n,
  e <= n -> S e <= S n.
Proof.
  intros.
  induction H.
  apply le_n.
  apply le_S.
  apply IHle.
Qed.

Lemma blt_false : forall e n,
  false = blt_nat e n -> n <= e.
Proof.
  induction e; intros.
  Case "e = 0".
    induction n.
    SCase "n = 0".
      apply le_n.
    SCase "n = S n".
      inversion H.
  Case "e = S e".
    induction n.
    SCase "n = 0".
      apply O_le_n.
    SCase "n = S n".
      apply blt_S in H.
      apply IHe in H.
      apply le_imp_le_S in H.
      auto.
Qed.

Lemma head_app l1 l2 (H : l1 <> []) :
  head (l1 ++ l2) = head l1.
Proof.
  induction l1.
  Case "l1 = []".
    assert ([] = []).
    SCase "Proof of assertion".
      reflexivity.

    apply H in H0.
    inversion H0.
  Case "l1 = n :: l1".
    auto.
Qed.

Lemma head_add : forall e t,
  head (inorder (add e t)) = head (inorder t)
  \/ head (inorder (add e t)) = e.
Proof.
  intros.
  induction t.
  Case "t = leaf".
    auto.
  Case "t = node t1 n t2".
    simpl in *.
    destruct compare.
    SCase "Lt".
      rewrite <- inorder_balancing.
      simpl.
      rewrite head_app.
      remember t1 as x; destruct x.
      SSCase "t1 = leaf".
        auto.
      SSCase "t1 = node x1 n0 x2".
        inversion IHt1.
        left.
        rewrite head_app.
        apply H.
        apply inorder_node.
        right.
        apply H.
        apply inorder_add_node.
    SCase "Eq".
      remember t1 as x; destruct x.
      SSCase "t1 = leaf".
        auto.
      SSCase "t1 = node x1 n0 x2".
        rewrite head_app.
        simpl.
        left.
        rewrite head_app.
        auto.

        unfold not. intros.
        apply app_nil in H.
        inversion H.

        apply inorder_node.
    SCase "Gt".
      rewrite <- inorder_balancing.
      simpl.
      remember t1 as x; destruct x.
      SSCase "t1 = leaf".
        auto.
      SSCase "t1 = node x1 n0 x2".
        simpl.
        rewrite head_app.
        remember x1 as y; destruct y.
        SSSCase "x1 = leaf".
          auto.
        SSSCase "x1 = node y1 n1 y2".
          rewrite head_app.
          left.
          rewrite head_app.
          rewrite head_app.
          auto.
          apply inorder_node.
          unfold not. intros.
          apply app_nil in H.
          inversion H.
          apply inorder_node.
          unfold not. intros.
          apply app_nil in H.
          inversion H.
Qed.

Lemma sorted_add : forall e n t2,
  sorted (n :: inorder t2) -> 
  sorted (inorder (add e t2)) ->
  false = blt_nat e n ->
  sorted (n :: inorder (add e t2)).
Proof.
  intros.
  apply sorted_cons'.
  split.
  Case "left".
    left.
    remember t2 as x; destruct x.
    SCase "t2 = leaf".
      simpl.
      apply blt_false.
      apply H1.
    SCase "t2 = node x1 n0 x2".

      assert (head (inorder (add e t2)) = head (inorder t2)
              \/ head (inorder (add e t2)) = e).
        apply head_add.

      inversion H2.
      rewrite Heqx.
      rewrite H3.
      rewrite Heqx in H.
      rewrite sorted_cons' in H.
      inversion H.
      inversion H4.
      apply H6.
      rewrite H6 in Heqx.
      inversion Heqx.
      rewrite Heqx.
      rewrite H3.
      apply blt_false.
      apply H1.
  Case "right".
    apply H0.
Qed.

Lemma head_rightrotation : forall t,
  sorted (inorder t) -> head (inorder t) = head (inorder (rightrotation t)).
Proof.
  intros.
  induction t.
  Case "t = leaf".
    simpl. reflexivity.
  Case "t = node t1 n t2".
    rewrite tree_in_list in H.
    simpl.
    destruct t1.
    SCase "t1 = leaf".
      simpl. reflexivity.
    SCase "t1 = node t1_1 n0 t1_2".
      simpl in *.
      rewrite list_assoc.
      reflexivity.
Qed.

Lemma head_left : forall t,
  sorted (inorder t) /\ left t <> leaf
  -> head (inorder t) = head (inorder (left t)).
Proof.
  intros.
  inversion H.
  clear H.
  destruct t.
  Case "t = leaf".
    simpl. reflexivity.
  Case "t = node t1 n t2".
    simpl in *.
    rewrite head_app.
    reflexivity.
    destruct t1.
    SCase "t1 = leaf".

      assert (leaf = leaf).
      SSCase "Proof of assertion".
        reflexivity.

      apply H1 in H.
      inversion H.
    SCase "t1 = node t1_1 n0 t1_2".
      apply inorder_node.
Qed.

Lemma left_sorted : forall t,
  sorted (inorder t) -> sorted (inorder (left t)).
Proof.
  intros.
  induction t.
  Case "t = leaf".
    simpl. apply s_nil.
  Case "t = node t1 n t2".
    simpl.
    rewrite tree_in_list in H.
    apply sorted_app'' in H.
    inversion H.
    apply H0.
    unfold not. intros. inversion H0.
Qed.

Lemma value_right_sorted : forall t,
  sorted (inorder t) -> sorted (value t :: inorder (right t)).
Proof.
  intros.
  induction t.
  Case "t = leaf".
    simpl. apply s_one.
  Case "t = node t1 n t2".
    simpl.
    rewrite tree_in_list in H.
    apply sorted_app'' in H.
    inversion H.
    inversion H1.
    apply H2.

    unfold not. intros. inversion H0.
Qed.

Lemma last_leftrotation : forall t,
  last (inorder t) = last (inorder (leftrotation t)).
Proof.
  intros.
  induction t.
  Case "t = leaf".
    simpl. reflexivity.
  Case "t = node t1 n t2".
    simpl.
    destruct t2.
    SCase "t2 = leaf".
      simpl. reflexivity.
    SCase "t2 = node t2_1 n0 t2_2".
      simpl.
      rewrite list_assoc.
      reflexivity.
Qed.

Theorem sorted_inorder : forall e t,
  sorted (inorder t) -> sorted (inorder (add e t)).
Proof.
  intros.
  induction t.
  Case "t = leaf".
    simpl. apply s_one.
  Case "t = node t1 n t2".
    rewrite tree_in_list in H.
    apply sorted_app'' in H.
    inversion H.
    inversion H1.

    simpl in *.
    unfold compare.
    destruct beq_nat.
    SCase "beq_nat e n = true".
      simpl.
      apply sorted_app2.
      apply H0.
      apply H2.
      simpl.
      apply H3.

    SCase "beq_nat e n = false".
      remember (blt_nat e n) as x; destruct x.
      SSCase "blt_nat e n = true".
        rewrite <- inorder_balancing.
        simpl.
        apply sorted_app2.
        apply IHt1 in H0.
        apply H0.
        apply H2.
        simpl.
        apply last_add.
        apply Heqx.
        apply H3.

      SSCase "blt_nat e n = false".
        rewrite <- inorder_balancing.
        simpl.
        apply sorted_app2.
        apply H0.

        assert (sorted (n :: inorder t2)).
          apply H2.

        apply sorted_cons' in H2.
        inversion H2.
        apply IHt2 in H6.
        apply sorted_add.
        apply H4.
        apply H6.
        apply Heqx.
        simpl.
        apply H3.
        unfold not. intro. inversion H0.
Qed.