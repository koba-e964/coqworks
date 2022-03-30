(* Natural deduction for intuitionistic logic *)

Set Implicit Arguments.

Require Import fml natded.
Require Export fml natded.

Declare Scope natdec_scope.

Open Scope natdec_scope.

Inductive nj: natded_pre -> fml -> Set := 
  | nj_from_con: forall {p a}, natded_con a p -> nj p a
  | nj_and_i: forall {p a b}, nj p a -> nj p b -> nj p (a and b)
  | nj_and_e1: forall {p a b}, nj p (a and b) -> nj p a
  | nj_and_e2: forall {p a b}, nj p (a and b) -> nj p b 
  | nj_or_i1: forall {p a b}, nj p a -> nj p (a or b)
  | nj_or_i2: forall {p a b}, nj p b -> nj p (a or b)
  | nj_or_e: forall {p a b c},
    nj p (a or b) -> nj (p :: a) c -> nj (p :: b) c -> nj p c
  | nj_imp_i: forall {p a b}, nj (p :: a) b -> nj p (a ==> b)
  | nj_imp_e: forall {p a b}, nj p (a ==> b) -> nj p a -> nj p b
  | nj_bot_e: forall {p a}, nj p fml_bot -> nj p a
.

(* slightly higher than  ~ (at level 75) *)
Notation "p |-NJ- s" := (nj p s) (at level 70).
Notation "|-NJ- s" := (nj natded_pre_zero s) (at level 70).

Close Scope natdec_scope.
