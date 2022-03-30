(* Properties of natded *)

Set Implicit Arguments.

Require Import RelationClasses.
Require Import fml natded.
Require Export fml natded.

Inductive is_sub_pre: natded_pre -> natded_pre -> Prop :=
  | is_sub_pre_zero: forall p, is_sub_pre natded_pre_zero p
  | is_sub_pre_succ: forall p q a,
    natded_con a p -> is_sub_pre q p -> is_sub_pre (q :: a) p.

Proposition is_sub_pre_ind_r: forall p q a,
  is_sub_pre p q -> is_sub_pre p (q :: a).
intros p q a H.
induction H as [|q p b con_b_q H IHis_sub_pre].
+ apply is_sub_pre_zero.
+ apply is_sub_pre_succ.
  - apply natded_con_succ.
    exact con_b_q.
  - apply IHis_sub_pre.
Qed.

Proposition is_sub_pre_succ_monotone: forall p q a,
  is_sub_pre p q -> is_sub_pre (p :: a) (q :: a).
intros p q a H.
apply is_sub_pre_succ.
+ apply natded_con_zero.
+ apply is_sub_pre_ind_r.
  exact H.
Qed.

Proposition is_sub_pre_with_con: forall a p q,
  natded_con a p -> is_sub_pre p q -> natded_con a q.
intros a p q con_a_p Hpq.
induction con_a_p as [x a|a x b con_a_p IHHpq].
(* p = x :: a *)
+ inversion Hpq as [|s t b H].
  exact H.
(* p = x :: b *)
+ apply IHHpq.
  inversion Hpq as [|s t c con_b_q Hxq].
  exact Hxq.
Qed.

Proposition is_sub_pre_refl: Reflexive is_sub_pre.
intro p.
induction p as [| p IHp a].
+ apply is_sub_pre_zero.
+ apply is_sub_pre_succ.
  - apply natded_con_zero.
  - apply is_sub_pre_ind_r.
    apply IHp.
Qed.

Proposition is_sub_pre_trans: Transitive is_sub_pre.
intros p q r Hpq Hqr.
induction Hpq as [|q x a con_a_x Hxq IHHxq].
+ apply is_sub_pre_zero.
+ apply is_sub_pre_succ.
  - apply (is_sub_pre_with_con (a := a) (p := q) (q := r)).
    * exact con_a_x.
    * exact Hqr.
  - apply IHHxq.
    apply Hqr.
Qed.
