(* Natural deduction for intuitionistic logic *)

Set Implicit Arguments.

Require Import fml natded.

Declare Scope natdec_scope.

Open Scope natdec_scope.

Inductive nk: natded_pre -> fml -> Set := 
  | nk_from_con: forall {p a}, natded_con a p -> nk p a
  | nk_and_i: forall {p a b}, nk p a -> nk p b -> nk p (a and b)
  | nk_and_e1: forall {p a b}, nk p (a and b) -> nk p a
  | nk_and_e2: forall {p a b}, nk p (a and b) -> nk p b 
  | nk_or_i1: forall {p a b}, nk p a -> nk p (a or b)
  | nk_or_i2: forall {p a b}, nk p b -> nk p (a or b)
  | nk_or_e: forall {p a b c},
    nk p (a or b) -> nk (p ::: a) c -> nk (p ::: b) c -> nk p c
  | nk_imp_i: forall {p a b}, nk (p ::: a) b -> nk p (a ==> b)
  | nk_imp_e: forall {p a b}, nk p (a ==> b) -> nk p a -> nk p b
  | nk_bot_e: forall {p a}, nk p fml_bot -> nk p a
  | nk_dne: forall {p a}, nk p (fml_not (fml_not a)) -> nk p a
.

(* slightly higher than  ~ (at level 75) *)
Notation "p |-NK- s" := (nk p s) (at level 70).
Notation "|-NK- s" := (nk natded_pre_zero s) (at level 70).

Close Scope natdec_scope.

(* Constructs p |-NK- a where a is obviously in p. *)
Ltac nk_trivial := apply nk_from_con; natded_trivial.
