Require Import Arith.
Require Import Program.
Require Import Omega.
Parameters (var: Set)
           (sig: nat -> Set).

Axiom var_eq_dec: forall v1 v2: var, { v1 = v2 } + { v1 <> v2 }.

Inductive ilist (A: Set) : nat -> Set :=
| niln: ilist A 0
| consn: forall n, A -> ilist A n -> ilist A (S n)
.

Inductive fin : nat -> Set :=
| f0: fin 1
| fs: forall n, fin n -> fin (S n)
.

Definition dlist n (P: fin n -> Set): Set := forall (i: fin n), P i. 

Fixpoint fin_to_nat n (m: fin n): nat.
  destruct m _eqn: Heq.
  exact 0.
  apply S.
  apply (fin_to_nat n f).
Defined.


Variable axiom: Set.

Inductive term: Set :=
  | tm_var: var -> term
  | tm_cong: forall n (s: sig n), (fin n -> term) -> term
.

Inductive deriv: term -> term -> Set :=
| drv_refl: forall s, deriv s s
| drv_sym: forall s t, deriv s t -> deriv t s
| drv_trans: forall s t u, deriv s t -> deriv t u -> deriv s u
| drv_cong: forall n (s: sig n) (ss ts: fin n -> term), dlist n (fun x => deriv (ss x) (ts x)) -> deriv (tm_cong n s ss) (tm_cong n s ts). 

(* example: refl *)
Goal forall s, deriv s s.
      apply drv_refl.
Qed.

Fixpoint subst (s: term) (u: term) (x: var): term :=
  match s with
  | tm_var v =>
    if var_eq_dec v x then u else tm_var v
  | tm_cong n si t =>
    tm_cong n si (fun i : fin n => subst (t i) u x)
  end.

Section monoid_theory.
  Axiom mul_sig: sig 2.
  Definition mul: term -> term -> term :=
    fun a b : term =>
tm_cong 2 mul_sig
   (fun i0 : fin 2 =>
    match
      i0 in (fin n0) return (forall i1 : fin n0, i1 = i0 -> term)
    with
    | f0 => fun (i1 : fin 1) (_ : i1 = f0) => a
    | fs n0 f1 => fun (i1 : fin (S n0)) (_ : i1 = fs n0 f1) => b
    end i0 eq_refl).
  Print mul.
  Axiom e_sig: sig 0.
  Definition e: term.
                  apply (tm_cong 0 e_sig).
                  intro i.
                  inversion i.
  Defined.
  Axiom unit_law_l: forall s, deriv (mul e s) s.
  Axiom unit_law_r: forall s, deriv (mul s e) s.

  Theorem mul_well_defined: forall s1 s2 t1 t2, deriv s1 t1 -> deriv s2 t2 -> deriv (mul s1 s2) (mul t1 t2).
                                                  intros s1 s2 t1 t2 H H0.
                                                  apply drv_cong.
                                                  intro i.
                                                  destruct i _eqn:ieq.
                                                  exact H.
                                                  exact H0.
                                                  Qed.
End monoid_theory.

Section subst_closed.
  
End subst_closed.
