Set Implicit Arguments.

Require Import nj.

Goal forall a, |-NJ- a ==> a.
intro a.
  apply nj_imp_i.
  nj_trivial.
Qed.

Goal forall a b, |-NJ- a ==> b ==> a.
intros a b.
  apply nj_imp_i.
  apply nj_imp_i.
  nj_trivial.
Qed.

Lemma dn_intro: forall p a, p |-NJ- a ==> fml_not (fml_not a).
intros p a.
  apply nj_imp_i.
  apply nj_imp_i.
  apply (nj_imp_e (a := a) (b := fml_bot)); nj_trivial.
Qed.

Lemma transposition: forall a b,
  natded_pre_zero ::: a |-NJ- b -> natded_pre_zero ::: fml_not b |-NJ- fml_not a.
intros a b H.
  apply nj_imp_i.
  apply (nj_imp_e (a := b) (b := fml_bot)).
  + nj_trivial.
  +
    admit.
Admitted.

Goal forall a, |-NJ- fml_not (fml_not (fml_not a)) ==> fml_not a.
intro a.
  apply nj_imp_i.
  apply transposition.
  apply (nj_imp_e (a := a)).
  + apply dn_intro.
  + nj_trivial.
Qed.
