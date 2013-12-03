Require Import Basics.



Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S n' => oddb n'
  end
with oddb (n : nat) : bool :=
  match n with
    | O => false
    | S n' => evenb n'
  end.






Theorem negb_involutive : forall (b : bool), negb (negb b) = b.
Proof.
  intros b.
  destruct b; reflexivity.
Qed.



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










Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
  reflexivity.
  Case "n = S n'".
  simpl.
  inversion IHn'.
  rewrite -> H0.
  rewrite -> (negb_involutive (oddb n')).
  reflexivity.
Qed.