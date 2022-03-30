(* Definitions related to natural deduction
 * that are useful for both NJ and NK.
 *)

Set Implicit Arguments.

Require Import fml.

Declare Scope natded_scope.

(* Set of premises *)
Inductive natded_pre: Set :=
  | natded_pre_zero: natded_pre
  | natded_pre_succ: natded_pre -> fml -> natded_pre.

Infix "::" := natded_pre_succ (at level 60, right associativity): natded_scope.

Open Scope natded_scope.

(* Assertion that a set of premises contains a formula. *)
Inductive natded_con: fml -> natded_pre -> Prop :=
  | natded_con_zero: forall {p a}, natded_con a (p :: a)
  | natded_con_succ: forall {a p b}, natded_con a p -> natded_con a (p :: b).
