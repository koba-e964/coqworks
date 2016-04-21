Require Import Coq.Program.Tactics.

Module Type Monoid.
  Parameter M: Type.
  Parameter e: M.
  Parameter mult: M -> M -> M.
  Axiom mult_e_l:
    forall x, mult e x = x.
  Axiom mult_e_r:
    forall x, mult x e = x.
  Axiom mult_assoc:
    forall x y z, mult x (mult y z) = mult (mult x y) z.
End Monoid.

Module list_bool_Monoid <: Monoid.
  Definition M := list bool.
  Definition e: M := nil.
  Definition mult x y: M := app x y.
  Proposition mult_e_l:
    forall x, mult e x = x.
    auto.
  Qed.
  Proposition mult_e_r:
    forall x, mult x e = x.
    induction x; auto.
    unfold mult.
    simpl.
    unfold mult in IHx.
    rewrite IHx.
    reflexivity.
  Qed.
  Proposition mult_assoc:
    forall x y z, mult x (mult y z) = mult (mult x y) z.
    Require Import List.
    apply app_assoc.
  Qed.
End list_bool_Monoid.

Print Monoid.
Print list_bool_Monoid.

Module MonoidExponential (M: Monoid).
  Fixpoint exp (x: M.M) (n: nat): M.M :=
    match n with 
    | 0 => M.e
    | S n' => M.mult x (exp x n')
    end.
  Proposition exp_law:
    forall n m x, M.mult (exp x n) (exp x m) = exp x (n + m).
  induction n.
  simpl.
  intros.
  rewrite M.mult_e_l.
  auto.
  (* step *)
  simpl.
  intros.
  rewrite <- M.mult_assoc.
  rewrite IHn.
  auto.
  Qed.
End MonoidExponential.

Module list_bool_Exponential.
  Include list_bool_Monoid.
  Include MonoidExponential list_bool_Monoid.
End list_bool_Exponential.

