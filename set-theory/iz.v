Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Image.

Definition edge X := X -> X -> Prop.

Section bisim.

Variables (X: Type) (A: edge X)
  (Y: Type) (B: edge Y).
Definition is_bisimulation (r: X -> Y -> Prop) : Prop :=
 (forall c1 c2 d2, (A c1 c2 /\ r c2 d2 -> exists d1, B d1 d2 /\ r c1 d1)) /\
 (forall d1 d2 c2, (B d1 d2 /\ r c2 d2 -> exists c1, A c1 c2 /\ r c1 d1)).

End bisim.

Section set_relation.
Variables (X: Type) (A: edge X) (a: X)
  (Y: Type) (B: edge Y) (b: Y).
Definition set_equal: Prop :=
  exists r, is_bisimulation X A Y B r /\ r a b.
End set_relation.

Definition set_member (X: Type) (A: edge X) (a: X)
  (Y: Type) (B: edge Y) (b: Y): Prop :=
  exists z, set_equal X A a Y B z /\ B z b.

Definition set_subset (X: Type) (A: edge X) (a: X)
  (Y: Type) (B: edge Y) (b: Y): Prop :=
  forall Z C c, set_member Z C c X A a -> set_member Z C c Y B b.


Definition sum X Y := (X -> Prop) -> (Y -> Prop) -> Prop.
Definition inl {X Y} (a: X): sum X Y := fun p _ => p a.
Definition inr {X Y} (b: Y): sum X Y := fun _ q => q b.
Definition out {X Y} : sum X Y := fun _ _ => False.

Definition opt X := (X -> Prop) -> Prop.
Definition some {X} x: opt X := fun f => f x.
Definition none {X}: opt X := fun _ => False.

Definition cnat := forall X, (X -> X) -> X -> X.
Definition zero: cnat := fun f x => x.
Definition succ (n: cnat): cnat := fun X f x => f (n X f x).
Definition cle (n: cnat) (m: cnat) := forall P: cnat -> Prop, P n -> (forall z, P z -> P (succ z)) -> P m.
Definition clt n m := cle (succ n) m.
Definition wf_nat n := cle zero n.

Proposition inl_inr_disj: forall X Y (x: X) (y: Y), inl (Y := Y) x <> inr y.
intros X Y x y H.
specialize (equal_f (A := X -> Prop) (B := (Y -> Prop) -> Prop) H (fun _ => False)).
intro H0.
specialize (equal_f H0 (fun _ => True)).
unfold inl, inr.
intro H1.
rewrite H1.
exact I.
Qed.


Proposition inl_out_disj: forall X Y (x: X), inl (Y := Y) x <> out.
intros X Y x H.
specialize (equal_f (A := X -> Prop) (B := (Y -> Prop) -> Prop) H (fun _ => True)).
intro H0.
specialize (equal_f H0 (fun _ => True)).
unfold inl, out.
intro H1.
rewrite <- H1.
exact I.
Qed.

Proposition inr_out_disj: forall X Y (y: Y), inr (X := X) y <> out.
intros X Y y H.
specialize (equal_f (A := X -> Prop) (B := (Y -> Prop) -> Prop) H (fun _ => True)).
intro H0.
specialize (equal_f H0 (fun _ => True)).
unfold inr, out.
intro H1.
rewrite <- H1.
exact I.
Qed.

Proposition inl_inj: forall X Y, injective _ _(inl (X := X) (Y := Y)).
intros X Y x1 x2 H.
specialize (equal_f H (fun z => z = x1)).
intro H0.
specialize (equal_f H0 (fun _ => True)).
unfold inl.
intro.
symmetry.
rewrite <- H1.
auto.
Qed.

Proposition inr_inj: forall X Y, injective _ _ (inr (X := X) (Y := Y)).
intros X Y y1 y2 H.
specialize (equal_f H (fun _ => True)).
intro H0.
specialize (equal_f H0 (fun z => z = y2)).
unfold inr.
intro.
rewrite H1.
auto.
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


(* empty *)

Definition empty_c := forall X, (X -> X) -> X -> X.
Definition empty_e: edge empty_c := fun _ _ => False.
Definition empty_b: empty_c := fun _ x => x.

Theorem axiom_empty: forall X A a, ~ set_member X A a empty_c empty_e empty_b.
intros X A a H.
destruct H as [x [H H0]].
auto.
Qed.

(* pair *)

Section pair.

Variables (X: Type) (A: edge X) (a: X) (Y: Type) (B: edge Y) (b: Y).
Definition pair_c := sum X Y.
Definition pair_e: edge (sum X Y) :=
  fun c1 c2 =>
    (exists a1 a2, c1 = inl a1 /\ c2 = inl a2 /\ A a1 a2) \/
    (exists b1 b2, c1 = inr b1 /\ c2 = inr b2 /\ B b1 b2) \/
    (c1 = inl a /\ c2 = out) \/
    (c1 = inr b /\ c2 = out).
Definition pair_b: pair_c := out.

End pair.


Lemma inl_pair_set_equal: forall Z C c X A a Y B b,
  set_equal Z C c (pair_c X Y) (pair_e X A a Y B b) (inl a)
  <-> set_equal Z C c X A a.

split; intro H.
destruct H as [r [H H0]].
exists (fun z x => r z (inl x)).
split; auto; clear H0 c.
destruct H as [H H0].
split.
clear H0.
intros c1 c2 d2.
intros H1; destruct H1 as [H1 H2].
specialize (H c1 c2 (inl d2)).
destruct H as [d1 H3].
tauto.
destruct H3 as [H H3].
assert (exists x1, d1 = inl x1 /\ A x1 d2).
  destruct H as [H|[H|[H|H]]].
  destruct H as [a1 [a2 [H [H5 H6]]]].
  exists a1.
  apply inl_inj in H5.
  rewrite <- H5 in H6.
  tauto.
  destruct H as [_ [b2 [_ [H _]]]].
  apply False_ind; apply (inl_inr_disj _ _ d2 b2); auto.
  apply False_ind; apply (inl_out_disj _ Y d2); tauto.
  apply False_ind; apply (inl_out_disj _ Y d2); tauto.

destruct H0 as [x1 [H0 H4]].
exists x1.
rewrite <- H0.
tauto.

clear H.
intros d1 d0 c0 H1.
destruct H1 as [H1 H2].
admit.

(* if part *)


Admitted.

Lemma inr_pair_set_equal: forall Z C c X A a Y B b,
  set_equal Z C c (pair_c X Y) (pair_e X A a Y B b) (inr b)
  <-> set_equal Z C c Y B b.
Admitted.

Theorem pair_axiom:
  forall X A a Y B b Z C c, set_member Z C c (pair_c X Y) (pair_e X A a Y B b) (pair_b X Y)
    <-> set_equal Z C c X A a \/ set_equal Z C c Y B b.
split.


(* z in {x, y} -> z = x \/ z = y *)
intros H.
destruct H as [sb [H H0]].
unfold pair_b in H0.
case H0 as [H0| [H0| [H0| H0]]].

(* case 1 *)
destruct H0 as [a1 [a2 H0]].
absurd (inl (Y := Y) a2 = out).
apply (inl_out_disj X Y a2).
symmetry.
tauto.

(* case 2 *)
destruct H0 as [b1 [b2 H0]].
absurd (inr (X := X) b2 = out).
apply (inr_out_disj X Y b2).
symmetry.
tauto.

(* case 3 *)
destruct H0 as [H0 _].
left.
rewrite H0 in H.
apply inl_pair_set_equal in H.
auto.

(* case 4 *)

destruct H0 as [H0 _].
right.
rewrite H0 in H.
apply inr_pair_set_equal in H.
auto.

(* if part *)
intros H.
destruct H as [H | H].

  (* z = x *)
  unfold set_member.
  exists (inl a).
  split.
  apply inl_pair_set_equal; auto.
  unfold pair_e.
  tauto.
  (* z = y *)
  unfold set_member.
  exists (inr b).
  split.
  apply inr_pair_set_equal; auto.
  unfold pair_e.
  tauto.
Qed.


Section pow.

Variable X: Type.
Variables  (A: edge X) (a: X).
Definition pow_c := sum X (X -> Prop).
Definition pow_e (b1 b2: pow_c): Prop :=
  (exists a1 a2, b1 = inl a1 /\ b2 = inl a2 /\ A a1 a2)
  \/ (exists a1 p, b1 = inl a1 /\ b2 = inr p /\ A a1 a /\ p a1)
  \/ (exists p, b1 = inl p /\ b2 = out).
Definition pow_b: pow_c := out.
End pow.

Theorem power_axiom: forall X A a Y B b,
  set_member X A a (pow_c Y) (pow_e Y B b) (pow_b Y) <-> set_subset X A a Y B b.
Admitted.

Definition U :=
  (forall X: Type, (X -> X -> Prop) -> X -> Prop) -> Prop.

Definition i: forall X: Type, (X -> X -> Prop) -> X -> U.
intros X A a f.
exact (f X A a).
Defined.

Definition set (u: U): Prop :=
  exists X A a, u = i X A a.

Definition ueq (u1 u2: U): Prop := 
exists X A a Y B b, u1 = i X A a /\ u2 = i Y B b /\ set_equal X A a Y B b.

Definition elt (u1 u2: U): Prop :=
  exists X A a Y B b, u1 = i X A a /\ u2 = i Y B b /\ set_member X A a Y B b.

