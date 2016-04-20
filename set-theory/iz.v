Require Import Coq.Logic.FunctionalExtensionality.


Definition is_bisimulation (X: Type) (A: X -> X -> Prop)
  (Y: Type) (B: Y -> Y -> Prop) (r: X -> Y -> Prop) : Prop :=
 forall c1 c2 d2, (A c1 c2 /\ r c2 d2 -> exists d1, B d1 d2 /\ r c1 d1) /\
 forall d1 d2 c2, (B d1 d2 /\ r c2 d2 -> exists c1, A c1 c2 /\ r c1 d1).

Definition set_equal (X: Type) (A: X -> X -> Prop) (a: X)
  (Y: Type) (B: Y -> Y -> Prop) (b: Y): Prop :=
  exists r, is_bisimulation X A Y B r /\ r a b.

Definition set_member (X: Type) (A: X -> X -> Prop) (a: X)
  (Y: Type) (B: Y -> Y -> Prop) (b: Y): Prop :=
  exists z, set_equal X A a Y B z /\ B z b.


Definition sum X Y := (X -> Prop) -> (Y -> Prop) -> Prop.
Definition inl X Y (a: X): sum X Y := fun p _ => p a.
Definition inr X Y (b: Y): sum X Y := fun _ q => q b.
Definition out X Y : sum X Y := fun _ _ => False.

Definition opt X := (X -> Prop) -> Prop.
Definition some X x: opt X := fun f => f x.
Definition none X: opt X := fun _ => False.

Definition cnat := forall X, (X -> X) -> X -> X.
Definition zero: cnat := fun f x => x.
Definition succ (n: cnat): cnat := fun X f x => f (n X f x).
Definition cle (n: cnat) (m: cnat) := forall P: cnat -> Prop, P n -> (forall z, P z -> P (succ z)) -> P m.
Definition clt n m := cle (succ n) m.
Definition wf_nat n := cle zero n.

Lemma inl_inr_disj: forall X Y x y, inl X Y x <> inr X Y y.
intros X Y x y H.
specialize (equal_f (A := X -> Prop) (B := (Y -> Prop) -> Prop) H (fun _ => False)).
intro H0.
specialize (equal_f H0 (fun _ => True)).
unfold inl, inr.
intro H1.
rewrite H1.
exact I.
Qed.


Lemma inl_out_disj: forall X Y x, inl X Y x <> out X Y.
intros X Y x H.
specialize (equal_f (A := X -> Prop) (B := (Y -> Prop) -> Prop) H (fun _ => True)).
intro H0.
specialize (equal_f H0 (fun _ => True)).
unfold inl, out.
intro H1.
rewrite <- H1.
exact I.
Qed.

Lemma inr_out_disj: forall X Y y, inr X Y y <> out X Y.
intros X Y y H.
specialize (equal_f (A := X -> Prop) (B := (Y -> Prop) -> Prop) H (fun _ => True)).
intro H0.
specialize (equal_f H0 (fun _ => True)).
unfold inr, out.
intro H1.
rewrite <- H1.
exact I.
Qed.



Goal forall n, cle n n.
intros n P H H0.
auto.
Qed.

Goal forall l m n, cle l m -> cle m n -> cle l n.
intros l m n H H0 P H1 H2.
apply H0.
apply H.
apply H1.
apply H2.
apply H2.
Qed.

Definition edge X := X -> X -> Prop.

(* pair *)


Definition pair_c X (A: edge X) (a: X) Y (B: edge Y) (b: Y) := sum X Y.
Definition pair_e X (A: edge X) (a: X) Y (B: edge Y) (b: Y): edge (sum X Y) := 
  fun b1 b2 =>
    (exists a1 a2, b1 = inl X Y a1 /\ b2 = inl X Y a2 /\ A a1 a2).
Definition pair_b X (A: edge X) (a: X) Y (B: edge Y) (b: Y) := out X Y.


Theorem pair_axiom:
  forall X A a Y B b Z C c, set_member Z C c (pair_c X A a Y B b) (pair_e X A a Y B b) (pair_b X A a Y B b)
    <-> set_equal Z C c X A a \/ set_equal Z C c Y B b.
split.

intros H.
destruct H as [base H].
destruct H as [H H0].
destruct H as [r H].
destruct H as [H H1].
destruct H0 as [a1 H0].
unfold pair_b in H0.
destruct H0 as [a2 H0].
destruct H0 as [H0 H2].
destruct H2 as [H2 H3].
(* out = inl *)
symmetry in H2.
apply inl_out_disj in H2.
case H2.


intros H.
destruct H as [H | H]; destruct H as [r [H H1]].

  unfold set_member.
  exists (inl X Y a).
  split.
  unfold set_equal.
  exists (fun z t => exists x, t = inl X Y x /\ r z x).
  split.
  unfold is_bisimulation, pair_c, pair_e.
  intros c1 c2 d2.
  split.
  intros H2; destruct H2 as [H2 [x [H3 H4]]].
  Admitted.
  simpl.


Definition U :=
  (forall X: Type, (X -> X -> Prop) -> X -> Prop) -> Prop.

Definition i: forall X: Type, (X -> X -> Prop) -> X -> U.
intros X A a f.
exact (f X A a).
Defined.

