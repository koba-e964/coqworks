Set Implicit Arguments.

Require Import natded_ext nj.

Theorem nj_weakening: forall p q a, is_sub_pre p q -> nj p a -> nj q a.
fix IH 5.
intros p q.
intros a Hpq Tqa.
inversion Tqa.
+ apply nj_from_con.
  apply (is_sub_pre_with_con H Hpq).
+ apply nj_and_i; apply (IH p _ _ Hpq).
  - apply H.
  - apply H0.
+ apply (nj_and_e1 (b := b)).
  apply (IH p _ _ Hpq).
  exact H.
+ apply (nj_and_e2 (a := a0)).
  apply (IH p _ _ Hpq).
  exact H.
+ apply nj_or_i1.
  apply (IH p _ _ Hpq).
  apply H.
+ apply nj_or_i2.
  apply (IH p _ _ Hpq).
  apply H.
+ apply (IH p _ _ Hpq) in H.
  apply (IH (p :: a0) (q :: a0) _) in H0.
  apply (IH (p :: b) (q :: b) _) in H1.
  apply (nj_or_e H H0 H1).
  (* prove p::a0 <= q::a0 *)
  apply (is_sub_pre_succ_monotone _ Hpq).
  apply (is_sub_pre_succ_monotone _ Hpq).
+ apply (IH (p :: a0) (q :: a0) _) in H.
  apply (nj_imp_i H).
  (* prove p::a0 <= q::a0 *)
  apply (is_sub_pre_succ_monotone _ Hpq).
+ apply (IH p _ _ Hpq) in H, H0.
  apply (nj_imp_e H H0).
+ apply (IH p _ _ Hpq) in H.
  apply (nj_bot_e H).
Qed.