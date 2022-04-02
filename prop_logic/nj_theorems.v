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
  exact (IH p _ _ Hpq H).
+ apply (nj_and_e2 (a := a0)).
  apply (IH p _ _ Hpq H).
+ apply nj_or_i1.
  apply (IH p _ _ Hpq H).
+ apply nj_or_i2.
  apply (IH p _ _ Hpq H).
+ apply (IH p _ _ Hpq) in H.
  apply (IH (p ::: a0) (q ::: a0) _) in H0.
  apply (IH (p ::: b) (q ::: b) _) in H1.
  apply (nj_or_e H H0 H1).
  (* prove p::a0 <= q::a0 *)
  rewrite Hpq.
  reflexivity.
  rewrite Hpq.
  reflexivity.
+ apply (IH (p ::: a0) (q ::: a0) _) in H.
  apply (nj_imp_i H).
  (* prove p::a0 <= q::a0 *)
  rewrite Hpq.
  reflexivity.
+ apply (IH p _ _ Hpq) in H, H0.
  apply (nj_imp_e H H0).
+ apply (IH p _ _ Hpq) in H.
  apply (nj_bot_e H).
Qed.

Require Import RelationClasses Setoid.

Add Morphism nj with signature is_sub_pre ++> eq ==> (fun A B => inhabited (A -> B)) as nj_monotone.
intros p q Hpq a.
apply inhabits.
exact (nj_weakening Hpq).
Qed.

Lemma nj_dni: forall p a, p |-NJ- a -> p |-NJ- fml_not (fml_not a).
intros p a Hpa.
apply nj_imp_i.
apply (nj_imp_e (a := a)).
+ apply nj_from_con.
  apply natded_con_zero.
+ assert (H: is_sub_pre p (p ::: fml_not a)).
  { apply is_sub_pre_ind_r; reflexivity. }
  exact (nj_weakening H Hpa).
Qed.
