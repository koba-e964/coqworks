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
  | id_weaken: forall {g s t}, int_deriv g t -> int_deriv (con_cons g s) t

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
  | cd_ne: forall g s, classic_deriv (con_cons g (fml_not s)) fml_bot -> classic_deriv g s
  | cd_weaken: forall {g s t}, classic_deriv g t -> classic_deriv (con_cons g s) t
.

Definition is_id_derivable (f: fml): Prop := exists dt: int_deriv con_empty f, True.
Definition is_cd_derivable (f: fml): Prop := exists dt: classic_deriv con_empty f, True.

Ltac id_var_con := apply id_var; repeat (try apply var_zero; apply var_succ).

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
apply id_weaken.
exact tr.
apply id_var.
apply var_zero.
Qed.

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
apply cd_weaken; apply id_to_cd; auto.
Defined.

Theorem id_then_cd: forall s, is_id_derivable s -> is_cd_derivable s.
intros s H.
destruct H as [tr _].
exists (id_to_cd tr).
auto.
Qed.


Definition id_ii_inv {g s t} (id: int_deriv g (fml_imp s t)): int_deriv (con_cons g s) t.
apply (id_ie _ s).
apply id_weaken; auto.
id_var_con.
Defined.

Theorem id_swap: forall {g s t u}, int_deriv (con_cons (con_cons g s) t) u -> int_deriv (con_cons (con_cons g t) s) u.
intros g s t u H.
apply (id_ie _ t).
apply id_ii_inv.
apply id_weaken.
apply id_ii.
apply id_ii; auto.
id_var_con.
Defined.

Definition id_contrapose {g s t} (id: int_deriv (con_cons g s) t): int_deriv (con_cons g (fml_not t)) (fml_not s).
apply id_ni.
apply (id_bi _ t).
apply id_ii_inv.
apply id_weaken.
apply id_ii; auto.
id_var_con.
Defined.


Definition id_doubleneg_monad {g s t}
  (id1: int_deriv g (fml_not (fml_not s))) (id2: int_deriv g (fml_imp s (fml_not (fml_not t))))
  : int_deriv g (fml_not (fml_not t)).
apply id_ni.
apply (id_bi _ (fml_not s)).
apply id_ni.
apply (id_bi _ (fml_not t)).
id_var_con.
apply id_ii_inv; apply id_weaken; auto.
apply id_weaken; auto.
Defined.

Fixpoint cd_to_doubleneg_id {g s} (cd: classic_deriv g s): int_deriv g (fml_not (fml_not s)).
destruct cd.
apply id_doubleneg.
apply id_var; auto.
(* ie *)
apply cd_to_doubleneg_id in cd1.
apply cd_to_doubleneg_id in cd2.
apply id_ni.
apply (id_bi _ (fml_not s)).
apply id_ni.
apply (id_bi _ (fml_not (fml_imp s t))).
apply id_ni.
apply (id_bi _ t).
apply (id_ie _ s); id_var_con.
id_var_con.
apply id_weaken; apply id_weaken.
exact cd1.
apply id_weaken.
exact cd2.
(* ii *)
apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_imp s t)).
apply id_ii.
apply id_be.
apply (id_bi _ (fml_not t)).
apply id_ni.
apply (id_bi _ (fml_imp s t)).
apply id_ii; id_var_con.
id_var_con.
apply id_swap; apply id_weaken; auto.
id_var_con.

(* ae1 *)
apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not (fml_and s t))).
apply id_ni.
apply (id_bi _ s).
apply (id_ae1 _ s t).
id_var_con.
id_var_con.
apply id_weaken; auto.


(* ae2 *)
apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not (fml_and s t))).
apply id_ni.
apply (id_bi _ t).
apply (id_ae2 _ s t).
id_var_con.
id_var_con.
apply id_weaken; auto.

(* ai *)

apply cd_to_doubleneg_id in cd1.
apply cd_to_doubleneg_id in cd2.
apply id_ni.
apply (id_bi _ (fml_not s)).
apply id_ni.
apply (id_bi _ (fml_not t)).
apply id_ni.
apply (id_bi _ (fml_and s t)).
apply id_ai.
id_var_con.
id_var_con.
id_var_con.
apply id_weaken; apply id_weaken; auto.
apply id_weaken; auto.

(* oe *)
apply cd_to_doubleneg_id in cd1.
apply cd_to_doubleneg_id in cd2.
apply id_oe; auto.

(* oi1 *)
apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not s)).
apply id_contrapose.
apply id_oi1; id_var_con.
apply id_weaken; auto.

(* oi2 *)
apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not t)).
apply id_contrapose.
apply id_oi2; id_var_con.
apply id_weaken; auto.

(* bi *)
apply cd_to_doubleneg_id in cd1.
apply cd_to_doubleneg_id in cd2.
apply id_ni.
apply (id_bi _ (fml_not (fml_not s))); apply id_weaken; auto.

(* be *)
apply cd_to_doubleneg_id in cd.
apply id_be.
apply (id_bi _ (fml_not fml_bot)).
apply id_ni; id_var_con.
auto.

(* ni *)

apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not s)).
apply id_weaken; apply id_ni.
apply (id_bi _ (fml_not fml_bot)).
apply id_ni; id_var_con.
auto.
id_var_con.

(* ne *)
apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not fml_bot)).
apply id_ni; id_var_con.
auto.

(* weaken *)
apply cd_to_doubleneg_id in cd.
apply id_weaken; auto.

Defined.



Theorem cd_then_doubleneg_id: forall s, is_cd_derivable s -> is_id_derivable (fml_not (fml_not s)).
intros s H.
destruct H as [tr _].
exists (cd_to_doubleneg_id tr).
auto.
Qed.

(* cut-eliminated version *)
Inductive int_deriv_ce: con -> fml -> Set :=
  | idce_var: forall g s, var g s -> int_deriv_ce g s
  | idce_ii: forall g s t, int_deriv_ce (con_cons g s) t -> int_deriv_ce g (fml_imp s t)
  | idce_ae1: forall g s t, int_deriv_ce g (fml_and s t) -> int_deriv_ce g s
  | idce_ae2: forall g s t, int_deriv_ce g (fml_and s t) -> int_deriv_ce g t
  | idce_ai : forall g s t, int_deriv_ce g s -> int_deriv_ce g t -> int_deriv_ce g (fml_and s t)
  | idce_oe: forall g s t u, int_deriv_ce (con_cons g s) u -> int_deriv_ce (con_cons g t) u -> int_deriv_ce (con_cons g (fml_or s t)) u
  | idce_oi1: forall g s t, int_deriv_ce g s -> int_deriv_ce g (fml_or s t)
  | idce_oi2: forall g s t, int_deriv_ce g t -> int_deriv_ce g (fml_or s t)
  | idce_bi: forall g s, int_deriv_ce g s -> int_deriv_ce g (fml_not s) -> int_deriv_ce g fml_bot
  | idce_be: forall g s, int_deriv_ce g fml_bot -> int_deriv_ce g s
  | idce_ni: forall g s, int_deriv_ce (con_cons g s) fml_bot -> int_deriv_ce g (fml_not s)
  | idce_weaken: forall {g s t}, int_deriv_ce g t -> int_deriv_ce (con_cons g s) t
.

Fixpoint id_eliminate_cuts g s (tree: int_deriv g s): int_deriv_ce g s.
inversion tree.
(* var *) apply idce_var; auto.
(* ie *) admit.
(* ii *) apply idce_ii.
exact (id_eliminate_cuts _ _ H).
(* ae1 *) apply (idce_ae1 _ _ t). apply id_eliminate_cuts; auto.
(* ae2 *) apply (idce_ae2 _ s0 _). apply id_eliminate_cuts; auto.
(* ai *) apply idce_ai; apply id_eliminate_cuts; auto.
(* oe *) apply idce_oe; apply id_eliminate_cuts; auto.
(* oi1 *) apply idce_oi1; apply id_eliminate_cuts; auto.
(* oi2 *) apply idce_oi2; apply id_eliminate_cuts; auto.
(* bi *) apply (idce_bi _ s0); apply id_eliminate_cuts; auto.
(* be *) apply idce_be; apply id_eliminate_cuts; auto.
(* ni *) apply idce_ni; apply id_eliminate_cuts; auto.
(* weaken *) apply idce_weaken; apply id_eliminate_cuts; auto.

Admitted.



Fixpoint id_disjunction s t (tree: int_deriv_ce con_empty (fml_or s t)):
  int_deriv_ce con_empty s + int_deriv_ce con_empty t.
    inversion tree.
    inversion H.
    inversion H; admit.
    admit.
    apply inl; auto.
    apply inr; auto.
    admit.
Admitted.


    
Theorem disjunctive_property: forall s t, is_id_derivable (fml_or s t) -> is_id_derivable s \/ is_id_derivable t.
intros s t H.
destruct H as [H _].
apply id_eliminate_cuts in H.
apply id_disjunction in H.
destruct H.
Admitted.
