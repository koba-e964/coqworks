Set Implicit Arguments.

Require Import fml hipc.

(* An example in https://plato.stanford.edu/entries/logic-intuitionistic/#AltForDedThe *)
Goal forall a: fml, |-HIPC- a ==> a.
intro a.

assert (l1 := hipc_by_axiom (hipc_axiom_then_1 a a)).
assert (l2 := hipc_by_axiom (hipc_axiom_then_2 a (a ==> a) a)).
assert (l4 := hipc_by_axiom (hipc_axiom_then_1 a (a ==> a))).
assert (l3 := hipc_mp l4 l2).
assert (l5 := hipc_mp l1 l3).
exact l5.
Qed.
