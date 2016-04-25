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

Definition is_id_derivable (f: fml): Prop := exists dt: int_deriv con_empty f, True.

Goal is_id_derivable (fml_not fml_bot).

compute.
assert (int_deriv con_empty (fml_not fml_bot)).
apply id_ni.
apply id_var.
apply var_zero.
exists H.
auto.
Qed.

Theorem disjunctive_property: forall s t, is_id_derivable (fml_or s t) -> is_id_derivable s \/ is_id_derivable t.
intros s t H.
destruct H as [H _].
destruct H.
Admitted.
