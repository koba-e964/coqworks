Set Implicit Arguments.

Require Import natded_ext nk.

Theorem nk_weakening: forall p q a, is_sub_pre p q -> nk p a -> nk q a.
fix IH 5.
intros p q.
intros a Hpq Tqa.
inversion Tqa.
+ apply nk_from_con.
  apply (is_sub_pre_with_con H Hpq).
+ apply nk_and_i; apply (IH p _ _ Hpq).
  - apply H.
  - apply H0.
+ apply (nk_and_e1 (b := b)).
  exact (IH p _ _ Hpq H).
+ apply (nk_and_e2 (a := a0)).
  apply (IH p _ _ Hpq H).
+ apply nk_or_i1.
  apply (IH p _ _ Hpq H).
+ apply nk_or_i2.
  apply (IH p _ _ Hpq H).
+ apply (IH p _ _ Hpq) in H.
  apply (IH (p ::: a0) (q ::: a0) _) in H0.
  apply (IH (p ::: b) (q ::: b) _) in H1.
  apply (nk_or_e H H0 H1).
  (* prove p::a0 <= q::a0 *)
  apply (is_sub_pre_succ_monotone _ Hpq).
  apply (is_sub_pre_succ_monotone _ Hpq).
+ apply (IH (p ::: a0) (q ::: a0) _) in H.
  apply (nk_imp_i H).
  (* prove p::a0 <= q::a0 *)
  apply (is_sub_pre_succ_monotone _ Hpq).
+ apply (IH p _ _ Hpq) in H, H0.
  apply (nk_imp_e H H0).
+ apply (IH p _ _ Hpq) in H.
  apply (nk_bot_e H).
+ apply (IH p _ _ Hpq) in H.
  apply (nk_dne H).
Qed.
