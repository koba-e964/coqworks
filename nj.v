Require Import ZArith.
Goal forall n : nat , n = n + O.
intros.
elim n.
simpl.
reflexivity.
intros.
simpl.
rewrite <- H.
reflexivity.
Qed.


Inductive MyProp : Set:=
| p1 :MyProp
| p2  :MyProp
| and : MyProp-> MyProp ->MyProp
| or : MyProp-> MyProp -> MyProp
| so : MyProp -> MyProp -> MyProp
| not : MyProp -> MyProp

.
Definition orIL (
