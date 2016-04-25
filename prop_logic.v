Variable ap: Set.
Inductive fml: Set :=
  | fml_var: ap -> fml
  | fml_and: fml -> fml -> fml
  | fml_or: fml -> fml -> fml
  | fml_imp: fml -> fml -> fml
  | fml_bot: fml
  | fml_not: fml -> fml.

Inductive con: Set :=
  | con_empty: con
  | con_cons: con -> fml -> con.

Inductive var: con -> fml -> Set :=
  | var_zero: forall g s, var (con_cons g s) s
  | var_succ: forall g s t, var g s -> var (con_cons g t) s.

Inductive int_deriv: con -> fml -> Set :=
  | id_var: forall g s, var g s -> int_deriv g s
  | id_ie: forall g s t, int_deriv g (fml_imp s t) -> int_deriv g s -> int_deriv g t
  | id_ii: forall g s t, int_deriv (con_cons g s) t -> int_deriv g (fml_imp s t)
  | id_ae1: forall g s t, int_deriv g (fml_and s t) -> int_deriv g s
  | id_ae2: forall g s t, int_deriv g (fml_and s t) -> int_deriv g t
  | id_ai : forall g s t, int_deriv g s -> int_deriv g t -> int_deriv g (fml_and s t)
  | id_oe: forall g s t u, int_deriv (con_cons g s) u -> int_deriv (con_cons g t) u -> int_deriv (con_cons g (fml_or s t)) u
  | id_oi1: forall g s t, int_deriv g s -> int_deriv g (fml_or s t)
  | id_oi2: forall g s t, int_deriv g t -> int_deriv g (fml_or s t)
  | id_bi: forall g s, int_deriv g s -> int_deriv g (fml_not s) -> int_deriv g fml_bot
  | id_be: forall g s, int_deriv g fml_bot -> int_deriv g s
  | id_ni: forall g s, int_deriv (con_cons g s) fml_bot -> int_deriv g (fml_not s)
.
Inductive classic_deriv: con -> fml -> Set :=
  | cd_var: forall g s, var g s -> classic_deriv g s
  | cd_ie: forall g s t, classic_deriv g (fml_imp s t) -> classic_deriv g s -> classic_deriv g t
  | cd_ii: forall g s t, classic_deriv (con_cons g s) t -> classic_deriv g (fml_imp s t)
  | cd_ae1: forall g s t, classic_deriv g (fml_and s t) -> classic_deriv g s
  | cd_ae2: forall g s t, classic_deriv g (fml_and s t) -> classic_deriv g t
  | cd_ai : forall g s t, classic_deriv g s -> classic_deriv g t -> classic_deriv g (fml_and s t)
  | cd_oe: forall g s t u, classic_deriv (con_cons g s) u -> classic_deriv (con_cons g t) u -> classic_deriv (con_cons g (fml_or s t)) u
  | cd_oi1: forall g s t, classic_deriv g s -> classic_deriv g (fml_or s t)
  | cd_oi2: forall g s t, classic_deriv g t -> classic_deriv g (fml_or s t)
  | cd_bi: forall g s, classic_deriv g s -> classic_deriv g (fml_not s) -> classic_deriv g fml_bot
  | cd_be: forall g s, classic_deriv g fml_bot -> classic_deriv g s
  | cd_ni: forall g s, classic_deriv (con_cons g s) fml_bot -> classic_deriv g (fml_not s)
  | cd_ne: forall g s, classic_deriv (con_cons g (fml_not s)) fml_bot -> classic_deriv g s.

Definition is_id_derivable (f: fml): Prop := exists dt: int_deriv con_empty f, True.
Definition is_cd_derivable (f: fml): Prop := exists dt: classic_deriv con_empty f, True.

Goal is_id_derivable (fml_not fml_bot).

compute.
assert (int_deriv con_empty (fml_not fml_bot)).
apply id_ni.
apply id_var.
apply var_zero.
exists H.
auto.
Qed.

Goal forall s, int_deriv con_empty (fml_imp s (fml_not (fml_not s))).
intro s.
apply id_ii.
apply id_ni.
apply (id_bi _ s).
apply id_var.
apply var_succ.
apply var_zero.
apply id_var.
apply var_zero.
Defined.


Definition id_doubleneg {g s} (tr: int_deriv g s): int_deriv g (fml_not (fml_not s)).
apply id_ni.
apply (id_bi _ s).
admit.
apply id_var.
apply var_zero.
Admitted.

Fixpoint id_to_cd {g s} (id: int_deriv g s): classic_deriv g s.
destruct id.
apply (cd_var _ _ v).
apply (cd_ie _ s); apply id_to_cd; auto.
apply (cd_ii _ s); apply id_to_cd; auto.
apply (cd_ae1 _ s t); apply id_to_cd; auto.
apply (cd_ae2 _ s t); apply id_to_cd; auto.
apply (cd_ai _ s t); apply id_to_cd; auto.
apply (cd_oe _ s t); apply id_to_cd; auto.
apply (cd_oi1 _ s t); apply id_to_cd; auto.
apply (cd_oi2 _ s t); apply id_to_cd; auto.
apply (cd_bi _ s); apply id_to_cd; auto.
apply (cd_be _ s); apply id_to_cd; auto.
apply (cd_ni _ s); apply id_to_cd; auto.
Defined.

Theorem id_then_cd: forall s, is_id_derivable s -> is_cd_derivable s.
intros s H.
destruct H as [tr _].
exists (id_to_cd tr).
auto.
Qed.

Fixpoint cd_to_doubleneg_id {g s} (cd: classic_deriv g s): int_deriv g (fml_not (fml_not s)).
destruct cd.
apply id_doubleneg.
apply id_var; auto.
Admitted.

Theorem cd_then_doubleneg_id: forall s, is_cd_derivable s -> is_id_derivable (fml_not (fml_not s)).
intros s H.
destruct H as [tr _].
exists (cd_to_doubleneg_id tr).
auto.
Qed.



Theorem disjunctive_property: forall s t, is_id_derivable (fml_or s t) -> is_id_derivable s \/ is_id_derivable t.
intros s t H.
destruct H as [H _].
destruct H.
Admitted.