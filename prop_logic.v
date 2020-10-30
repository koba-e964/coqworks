Variable ap: Set.
Inductive fml: Set :=
  | fml_var: ap -> fml
  | fml_and: fml -> fml -> fml
  | fml_or: fml -> fml -> fml
  | fml_imp: fml -> fml -> fml
  | fml_bot: fml
  | fml_not: fml -> fml.

Notation "s ==> t" := (fml_imp s t) (at level 80, right associativity).

Inductive con: Set :=
  | con_empty: con
  | con_cons: con -> fml -> con.

Inductive var: con -> fml -> Set :=
  | var_zero: forall g v, var (con_cons g (fml_var v)) (fml_var v)
  | var_succ: forall g s t, var g s -> var (con_cons g t) s.

Inductive int_deriv: con -> fml -> Set :=
  | id_self: forall g s, int_deriv (con_cons g s) s
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

Notation "c |-LJ- s" := (int_deriv c s) (at level 100).

Inductive classic_deriv: con -> fml -> Set :=
  | cd_self: forall g s, classic_deriv (con_cons g s) s
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

Fixpoint id_var g s (t: var g s): int_deriv g s.
induction t.
* apply id_self.
* apply id_weaken.
  exact IHt.
Defined.


Ltac id_var_con := apply id_var; repeat (try apply var_zero; apply var_succ).

Ltac in_env := repeat (try apply id_self; apply id_weaken).

Goal is_id_derivable (fml_not fml_bot).

compute.
assert (int_deriv con_empty (fml_not fml_bot)).
apply id_ni.
apply id_self.
exists H.
auto.
Qed.

Goal forall s, int_deriv con_empty (fml_imp s (fml_not (fml_not s))).
intro s.
apply id_ii.
apply id_ni.
apply (id_bi _ s).
in_env.
in_env.
Defined.




Definition id_doubleneg {g s} (tr: int_deriv g s): int_deriv g (fml_not (fml_not s)).
apply id_ni.
apply (id_bi _ s).
apply id_weaken.
exact tr.
apply id_self.
Defined.


Fixpoint id_to_cd {g s} (id: int_deriv g s): classic_deriv g s.
destruct id.
apply (cd_self _ s).
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
apply id_self.
Defined.

Theorem id_swap: forall {g s t u}, int_deriv (con_cons (con_cons g s) t) u -> int_deriv (con_cons (con_cons g t) s) u.
intros g s t u H.
apply (id_ie _ t).
apply id_ii_inv.
apply id_weaken.
apply id_ii.
apply id_ii; auto.
apply id_weaken.
apply id_self.
Defined.

Definition id_contrapose {g s t} (id: int_deriv (con_cons g s) t): int_deriv (con_cons g (fml_not t)) (fml_not s).
apply id_ni.
apply (id_bi _ t).
apply id_ii_inv.
apply id_weaken.
apply id_ii; auto.
apply id_weaken.
apply id_self.
Defined.


Definition id_doubleneg_monad {g s t}
  (id1: int_deriv g (fml_not (fml_not s))) (id2: int_deriv g (fml_imp s (fml_not (fml_not t))))
  : int_deriv g (fml_not (fml_not t)).
apply id_ni.
apply (id_bi _ (fml_not s)).
apply id_ni.
apply (id_bi _ (fml_not t)).
apply id_weaken.
apply id_self.
apply id_ii_inv; apply id_weaken; auto.
apply id_weaken; auto.
Defined.

Fixpoint cd_to_doubleneg_id {g s} (cd: classic_deriv g s): int_deriv g (fml_not (fml_not s)).
destruct cd.
apply id_doubleneg.
apply id_self; auto.
(* ie *)
apply cd_to_doubleneg_id in cd1.
apply cd_to_doubleneg_id in cd2.
apply id_ni.
apply (id_bi _ (fml_not s)).
apply id_ni.
apply (id_bi _ (fml_not (fml_imp s t))).
apply id_ni.
apply (id_bi _ t).
apply (id_ie _ s).
apply id_self.
in_env.
in_env.
in_env.
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
apply id_ii.
in_env.
in_env.
apply id_swap; apply id_weaken; auto.
apply id_self.

(* ae1 *)
apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not (fml_and s t))).
apply id_ni.
apply (id_bi _ s).
apply (id_ae1 _ s t).
in_env.
in_env.
apply id_weaken; auto.


(* ae2 *)
apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not (fml_and s t))).
apply id_ni.
apply (id_bi _ t).
apply (id_ae2 _ s t).
in_env.
in_env.
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
in_env.
in_env.
in_env.
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
apply id_oi1; in_env.
apply id_weaken; auto.

(* oi2 *)
apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not t)).
apply id_contrapose.
apply id_oi2; in_env.
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
apply id_ni; in_env.
auto.

(* ni *)

apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not s)).
apply id_weaken; apply id_ni.
apply (id_bi _ (fml_not fml_bot)).
apply id_ni; in_env.
auto.
in_env.

(* ne *)
apply cd_to_doubleneg_id in cd.
apply id_ni.
apply (id_bi _ (fml_not fml_bot)).
apply id_ni; in_env.
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

(* cut-eliminated LJ *)
Inductive int_deriv_ljc: con -> fml -> Set :=
  | idlj_init: forall g s, var g s -> int_deriv_ljc g s
  | idlj_ri: forall g s t, int_deriv_ljc (con_cons g s) t -> int_deriv_ljc g (fml_imp s t)
  | idlj_li: forall g s t u, int_deriv_ljc g s -> int_deriv_ljc (con_cons g t) u -> int_deriv_ljc (con_cons g (fml_imp s t)) u
  | idlj_ra : forall g s t, int_deriv_ljc g s -> int_deriv_ljc g t -> int_deriv_ljc g (fml_and s t)
  | idlj_la1: forall g s t u, int_deriv_ljc (con_cons g s) u -> int_deriv_ljc (con_cons g (fml_and s t)) u
  | idlj_la2: forall g s t u, int_deriv_ljc (con_cons g t) u -> int_deriv_ljc (con_cons g (fml_and s t)) u
  | idlj_lo: forall g s t u, int_deriv_ljc (con_cons g s) u -> int_deriv_ljc (con_cons g t) u -> int_deriv_ljc (con_cons g (fml_or s t)) u
  | idlj_ro1: forall g s t, int_deriv_ljc g s -> int_deriv_ljc g (fml_or s t)
  | idlj_ro2: forall g s t, int_deriv_ljc g t -> int_deriv_ljc g (fml_or s t)
  | idlj_r_weak: forall g s, int_deriv_ljc g fml_bot -> int_deriv_ljc g s
  | idlj_lb: forall g s, int_deriv_ljc (con_cons g fml_bot) s
  | idlj_rn: forall g s, int_deriv_ljc (con_cons g s) fml_bot -> int_deriv_ljc g (fml_not s)
  | idlj_ln: forall g s, int_deriv_ljc g s -> int_deriv_ljc (con_cons g (fml_not s)) fml_bot
  | idlj_l_weak: forall {g s t}, int_deriv_ljc g t -> int_deriv_ljc (con_cons g s) t
  | idlj_l_swap: forall {g s t u}, int_deriv_ljc (con_cons (con_cons g s) t) u
      -> int_deriv_ljc (con_cons (con_cons g t) s) u
  | idlj_l_contr: forall {g s t}, int_deriv_ljc (con_cons (con_cons g s) s) t -> int_deriv_ljc (con_cons g s) t
.

Notation "c |-LJc- s" := (int_deriv_ljc c s) (at level 100, no associativity).


(* Key admissible rule for cut-free LJ. *)
Fixpoint idljc_ie g s t (tr1: int_deriv_ljc (con_cons g s) t) (tr2: int_deriv_ljc g s)
  : int_deriv_ljc g t.
  inversion tr1.
(* var *)
+ clear H1 H0 g0 s0. 
  inversion H.
  - rewrite H2.
    exact tr2.
  - apply idlj_init.
    exact H3. 
(* -> r *)
+ clear H0 g0.
  apply idlj_ri.
  apply idlj_l_swap in H.
  apply (idljc_ie _ s _).
  exact H.
  apply idlj_l_weak.
  exact tr2.
(* -> l *)
+ admit.
(* /\ r *)
+ apply idlj_ra;
  apply (idljc_ie _ s); auto.
(* /\ l1 *)
+ clear H0.
  clear u.
  rewrite <- H1 in tr2, tr1.
  clear H1 s.
  clear H g0.
  inversion tr2.
  - inversion H.
admit.
(* /\ l2 *)
+ admit.
(* \/ l *)
+ admit.
(* \/ r1 *)
+ apply idlj_ro1; apply (idljc_ie _ s); auto.
(* \/ r2 *)
+ apply idlj_ro2; apply (idljc_ie _ s); auto.
(* weak r *)
+ apply idlj_r_weak; apply (idljc_ie _ s); auto.
(* bot l *)
+ admit.
(* not r *)
+ apply idlj_rn. admit.
(* not l *)
+ admit.
(* weak l *)
+ admit.
(* swap l *)
+ admit.
Admitted.

Fixpoint idljc_swap {g s t u} (tr: int_deriv_ljc (con_cons (con_cons g s) t) u)
  : int_deriv_ljc (con_cons (con_cons g t) s) u.
apply idlj_l_swap.
exact tr.
Defined.

Fixpoint idljc_self {g s}: int_deriv_ljc (con_cons g s) s.
induction s.
(* var *)
* apply idlj_init.
  apply var_zero.
(* and *)
* apply idlj_ra.
  - apply idlj_la1.
    apply IHs1.
  - apply idlj_la2.
    apply IHs2.
(* or *)
* apply idlj_lo.
  - apply idlj_ro1.
    apply IHs1.
  - apply idlj_ro2.
    apply IHs2.
(* imp *)
* apply idlj_ri.
  apply idljc_swap.
  apply idlj_li.
  - apply IHs1.
  - apply idljc_swap.
    apply idlj_l_weak.
    apply IHs2.
(* bot *)
* apply idlj_lb.
(* not *)
* apply idlj_rn.
  apply idljc_swap.
  apply idlj_ln.
  apply IHs.
Defined.


Definition idljc_ii_inv {g} s t (tr: int_deriv_ljc g (s ==> t)): int_deriv_ljc (con_cons g s) t.
apply (idljc_ie _ (s ==> t)).
- apply idlj_li.
  + apply idljc_self.
  + apply idljc_self.
- apply idlj_l_weak. exact tr.
Defined.
 

Definition idljc_ae1 {g} s t (tr: int_deriv_ljc g (fml_and s t)): int_deriv_ljc g s.
apply (idljc_ie g (fml_and s t) s).
apply idlj_la1.
apply idljc_self.
exact tr.
Defined.

Definition idljc_ae2 {g} s t (tr: int_deriv_ljc g (fml_and s t)): int_deriv_ljc g t.
apply (idljc_ie g (fml_and s t) t).
apply idlj_la2.
apply idljc_self.
exact tr.
Defined.

Definition idljc_ai {g} s t (tr1: int_deriv_ljc g s) (tr2: int_deriv_ljc g t): int_deriv_ljc g (fml_and s t)
:= idlj_ra g s t tr1 tr2.

Definition idljc_oe {g} s t u (tr1: int_deriv_ljc (con_cons g s) u) (tr2: int_deriv_ljc (con_cons g t) u):
  int_deriv_ljc (con_cons g (fml_or s t)) u
:= idlj_lo _ _ _ _ tr1 tr2.

Definition idljc_oi1 {g} s t (tr: int_deriv_ljc g s): int_deriv_ljc g (fml_or s t)
:= idlj_ro1 g s t tr.

Definition idljc_oi2 {g} s t (tr: int_deriv_ljc g t): int_deriv_ljc g (fml_or s t)
:= idlj_ro2 g s t tr.

Definition idljc_bi {g} s (tr1: int_deriv_ljc g s) (tr2: int_deriv_ljc g (fml_not s)): int_deriv_ljc g fml_bot.
apply (idljc_ie g (fml_not s)).
- apply idlj_ln.
  exact tr1.
- exact tr2.
Defined.

Definition idljc_be {g} s (tr: int_deriv_ljc g fml_bot): int_deriv_ljc g s
  := idlj_r_weak g s tr.

Definition idljc_ni {g} s (tr: int_deriv_ljc (con_cons g s) fml_bot): int_deriv_ljc g (fml_not s)
  := idlj_rn g s tr.

Definition idljc_weaken {g} s t (tr: int_deriv_ljc g t): int_deriv_ljc (con_cons g s) t
  := idlj_l_weak tr.


Fixpoint id_eliminate_cuts g s (tree: int_deriv g s): int_deriv_ljc g s.
inversion tree.
(* var *)
+ apply idljc_self.

(* ie *)
+ apply (idljc_ie _ s0).
  - apply idljc_ii_inv.
    apply id_eliminate_cuts.
    exact H.
  - apply id_eliminate_cuts; auto.
(* ii *)
+ apply idlj_ri.
  exact (id_eliminate_cuts _ _ H).
(* ae1 *)
+ apply (idljc_ae1 _ t). apply id_eliminate_cuts; auto.
(* ae2 *)
+ apply (idljc_ae2 s0 _). apply id_eliminate_cuts. exact H.
(* ai *)
+ apply idljc_ai; apply id_eliminate_cuts. exact H. exact H0.
(* oe *)
+ apply idljc_oe; apply id_eliminate_cuts; auto.
(* oi1 *)
+ apply idljc_oi1; apply id_eliminate_cuts; auto.
(* oi2 *)
+ apply idljc_oi2; apply id_eliminate_cuts; auto.
(* bi *)
+ apply (idljc_bi s0); apply id_eliminate_cuts; auto.
(* be *)
+ apply idljc_be; apply id_eliminate_cuts; auto.
(* ni *)
+ apply idljc_ni; apply id_eliminate_cuts; auto.
(* weaken *)
+ apply idljc_weaken; apply id_eliminate_cuts; auto.

Defined.


Fixpoint id_allow_cuts {g s} (tree: int_deriv_ljc g s): int_deriv g s.
inversion tree.
(* var *) apply id_var; auto. 
(* ri *)
+ apply id_ii. apply id_allow_cuts.
  auto.
(* li *)
+ apply (id_ie _ s0 _).
  - apply id_ii.
    apply (id_ie _ t).
    * apply id_ii.
      apply id_swap; apply id_weaken.
      apply id_swap; apply id_weaken.
      apply id_allow_cuts.
      exact H0.
    * apply id_ii_inv.
      apply id_self.
  - apply id_weaken.
    apply id_allow_cuts.
    exact H.
(* ra *)
+ apply (id_ai _ s0 _); apply id_allow_cuts; auto.
(* la1 *)
+ apply (id_ie _ s0 s).
  - apply id_weaken.
    apply id_ii.
    apply id_allow_cuts.
    exact H.
  - apply (id_ae1 _ _ t).
    apply id_self.
(* la2 *)
+ apply (id_ie _ t s).
  - apply id_weaken.
    apply id_ii.
    apply id_allow_cuts.
    exact H.
  - apply (id_ae2 _ s0 _).
    apply id_self.
(* lo *)
+ apply id_oe; apply id_allow_cuts; auto.
(* ro1 *)
+ apply (id_oi1 _ _ t); apply id_allow_cuts; auto.
(* ro2 *)
+ apply (id_oi2 _ s0 _); apply id_allow_cuts; auto.
(* r_weak *)
+ apply (id_be _ s); apply id_allow_cuts; auto.
(* lb *)
+ apply id_be.
  apply id_self.
(* rn *)
+ apply id_ni; apply id_allow_cuts; auto.
(* ln *)
+ apply (id_bi _ s0).
  - apply id_weaken.
    apply id_allow_cuts.
    exact H.
  - apply id_self.
(* weaken *)
+ apply id_weaken; apply id_allow_cuts; auto.
(* swap *)
+ apply id_swap.
  apply id_allow_cuts.
  exact H.
(* contr *)
+ admit.
Admitted.

Fixpoint id_disjunction s t (tree: int_deriv_ljc con_empty (fml_or s t)):
  int_deriv_ljc con_empty s + int_deriv_ljc con_empty t.
    inversion tree.
    inversion H.
    inversion H; admit.
    admit.
    apply inl; auto.
    admit.
Admitted.


    
Theorem disjunctive_property: forall s t, is_id_derivable (fml_or s t) -> is_id_derivable s \/ is_id_derivable t.
intros s t H.
destruct H as [H _].
apply id_eliminate_cuts in H.
apply id_disjunction in H.
destruct H.
left; exists (id_allow_cuts i); auto.
right; exists (id_allow_cuts i); auto.
Qed.
