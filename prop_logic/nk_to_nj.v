(* NK to NJ, especially Glivenko's theorem. *)

Set Implicit Arguments.

Require Import nj nk natded_ext nj_theorems nk_theorems.

Lemma dn_bind: forall p a b,
  p |-NJ- fml_not (fml_not a) -> p ::: a |-NJ- fml_not (fml_not b) ->
  p |-NJ- fml_not (fml_not b).
intros p a b Hpnna Hpannb.
apply nj_imp_i.
apply (nj_imp_e (a := fml_not a)).
+ refine (nj_weakening _ Hpnna).
  apply is_sub_pre_ind_r.
  reflexivity.
+ apply nj_imp_i.
  apply (nj_imp_e (a := fml_not b)).
  - refine (nj_weakening _ Hpannb).
    apply is_sub_pre_succ_monotone.
    apply is_sub_pre_ind_r.
    reflexivity.
  - nj_trivial.
Qed.

Lemma dn_functorial: forall p a b,
  p |-NJ- a ==> b -> p |-NJ- fml_not (fml_not a) ==> fml_not (fml_not b).
intros p a b Hpab.
apply nj_imp_i.
apply (dn_bind (a := a)).
+ nj_trivial.
+ apply nj_dni.
  apply (nj_imp_e (a := a)).
  - refine (nj_weakening _ Hpab).
    do 2 apply is_sub_pre_ind_r.
    reflexivity.
  - nj_trivial.
Qed.

Lemma dn_and: forall p a b,
  p |-NJ- fml_not (fml_not a) -> p |-NJ- fml_not (fml_not b) ->
  p |-NJ- fml_not (fml_not (a and b)).
intros p a b Hpnna Hpnnb.
apply (dn_bind (a := a) Hpnna).
apply (dn_bind (a := b)).
+ refine (nj_weakening _ Hpnnb).
  apply is_sub_pre_ind_r.
  reflexivity.
+ apply nj_dni.
  apply nj_and_i; nj_trivial.
Qed.

Lemma dn_imp: forall p a b,
  p ::: a |-NJ- fml_not (fml_not b) ->
  p |-NJ- fml_not (fml_not (a ==> b)).
intros p a b Hannb.
apply (nj_imp_e (a := a ==> fml_not (fml_not b))).
- do 2 apply nj_imp_i.
  apply (nj_imp_e (a := a ==> b)).
  + nj_trivial.
  + apply nj_imp_i.
    apply nj_bot_e.
    apply (nj_imp_e (a := fml_not b)).
    * apply (nj_imp_e (a := a)); nj_trivial.
    * apply nj_imp_i.
      apply (nj_imp_e (a := a ==> b)).
      -- nj_trivial.
      -- apply nj_imp_i.
         nj_trivial.
- exact (nj_imp_i Hannb).
Qed.

Theorem glivenko_general: forall p a, p |-NK- a -> p |-NJ- fml_not (fml_not a).
fix IH 3.
intros p a NKpa.
inversion_clear NKpa as [
p0 c con_c
|
(* and_e *)
|p0 c d Hpcd
|p0 c d Hpcd
(* or_i *)
|p0 c d Hpc
|p0 c d Hpd
(* or_e *)
| p0 c d e Hc_or_d Hc_to_e Hd_to_e
(* imp_i *)
| p0 c d Hc_to_d
(* imp_e *)
| p0 c d Hc_to_d Hc
(* bot_e *)
| p0 c Hbot
(* dne *)
| p0 c Hnnc
].
+ apply nj_dni.
  exact (nj_from_con con_c).
+ apply dn_and.
  apply (IH _ _ H).
  apply (IH _ _ H0).
+ apply IH in Hpcd.
  apply (dn_bind (a := a and d) Hpcd).
  apply nj_dni.
  apply (nj_and_e1 (b := d)).
  nj_trivial.
+ apply IH in Hpcd.
  apply (dn_bind (a := c and a) Hpcd).
  apply nj_dni.
  apply (nj_and_e2 (a := c)).
  nj_trivial.
+ apply IH in Hpc.
  apply (dn_bind Hpc).
  apply nj_dni.
  apply nj_or_i1.
  nj_trivial.
+ apply IH in Hpd.
  apply (dn_bind Hpd).
  apply nj_dni.
  apply nj_or_i2.
  nj_trivial.
+ apply IH in Hc_or_d, Hc_to_e, Hd_to_e.
  apply (dn_bind (Hc_or_d)).
  apply (nj_or_e (a := c) (b := d)).
  - nj_trivial.
  - refine (nj_weakening _ Hc_to_e).
    apply is_sub_pre_succ_monotone.
    apply is_sub_pre_ind_r; reflexivity.
  - refine (nj_weakening _ Hd_to_e).
    apply is_sub_pre_succ_monotone.
    apply is_sub_pre_ind_r; reflexivity.
+ apply IH in Hc_to_d.
  apply dn_imp.
  apply Hc_to_d.
+ apply IH in Hc_to_d, Hc.
  apply (dn_bind (a := c) Hc).
  apply (dn_bind (a := c ==> a)).
  - refine (nj_weakening _ Hc_to_d).
    apply is_sub_pre_ind_r; reflexivity.
  - apply nj_dni.
    apply (nj_imp_e (a := c)); nj_trivial.
+ apply IH in Hbot.
  apply nj_bot_e.
  apply (nj_imp_e Hbot).
  apply nj_imp_i; nj_trivial.
+ apply IH in Hnnc.
  apply (dn_bind Hnnc).
  nj_trivial.
Qed.

Corollary glivenko: forall a, |-NK- a -> |-NJ- fml_not (fml_not a).
apply glivenko_general.
Qed.

Proposition nj_to_nk: forall p a, p |-NJ- a -> p |-NK- a.
fix IH 3.
intros p a NJpa.
inversion_clear NJpa as [
p0 c con_c
|
(* and_e *)
|p0 c d Hpcd
|p0 c d Hpcd
(* or_i *)
|p0 c d Hpc
|p0 c d Hpd
(* or_e *)
| p0 c d e Hc_or_d Hc_to_e Hd_to_e
(* imp_i *)
| p0 c d Hc_to_d
(* imp_e *)
| p0 c d Hc_to_d Hc
(* bot_e *)
| p0 c Hbot
].
+ apply (nk_from_con con_c).
+ apply nk_and_i; apply IH; auto.
+ apply (nk_and_e1 (b := d)); apply IH; auto.
+ apply (nk_and_e2 (a := c)); apply IH; auto.
+ apply nk_or_i1; apply IH; auto.
+ apply nk_or_i2; apply IH; auto.
+ apply (nk_or_e (a := c) (b := d)); apply IH; auto.
+ apply nk_imp_i; apply IH; auto.
+ apply (nk_imp_e (a := c)); apply IH; auto.
+ apply nk_bot_e; apply IH; auto.
Qed.

Corollary nj_nk_equiconsistent: inhabited (|-NJ- fml_bot) <-> inhabited (|-NK- fml_bot).
split; apply inhabited_covariant.
+ apply nj_to_nk.
+ intro NKbot.
  apply glivenko in NKbot.
  apply (nj_imp_e NKbot).
  apply nj_imp_i; nj_trivial.
Qed.
