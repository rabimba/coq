Definition identity0 (x:nat) :=x.
Definition identity (A:Type) (x:A) :=x.
Definition identity3 {A:Type} (x:A) :=x.
Definition apply {A:Type} {B:Type} (f:A->B) (x:A) := f x.
Definition add x := fst x + snd x.
Eval compute in apply add (1,2).
Open Scope list_scope.
Notation "[a; .. ;b ]" := (a :: .. (b :: nil) .. ).
Fixpoint map {A:Type} {B:Type} (f:A->B) (x:list A) :=
 match x with
 |nil =>nil
 |(h::t) => (f h)::(map f t)
end.

Check map.

Eval compute in map add [(1,2); (3,4); (5,6)].
Eval compute in map (fun n => n+1) [1;2;3].

Definition compose {A B C:Type} (f:B->C) (g:A->B) :=
 (fun x=> f (g,x)).

Definition cool := compose (fun n=> n+1) (fun n => n*2).

Eval compute in cool 10.

Definition addx x := (fun y => x+y).

Eval compute in addx 3.
Eval compute in (addx 3) 4.
Eval compute in addx 3,4.

Definition someadd x y := x+y.

Eval compute in someadd 3.