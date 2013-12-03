Require Import Arith.

Fixpoint myle m n :=
match m with
|O => true
|S m2 => match n with
    |O=>false
    |S n2 => myle m2 n2
    end
end.

Theorem myle_complete:
 forall m n, m<=n -> (myle m n =true).

Proof.
intro m.
induction m.
intro n.
intro H.
simpl.
reflexivity.
intro n.
intro H.
simpl.
destruct n.
absurd (S m <= 0).
apply le_Sn_0.
apply H.
specialize (IHm n).
apply IHm.
apply le_S_n.
apply H.
Qed.