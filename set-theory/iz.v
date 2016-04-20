Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Image.

Definition edge X := X -> X -> Prop.

Definition is_bisimulation (X: Type) (A: edge X)
  (Y: Type) (B: edge Y) (r: X -> Y -> Prop) : Prop :=
 forall c1 c2 d2, (A c1 c2 /\ r c2 d2 -> exists d1, B d1 d2 /\ r c1 d1) /\
 forall d1 d2 c2, (B d1 d2 /\ r c2 d2 -> exists c1, A c1 c2 /\ r c1 d1).

Definition set_equal (X: Type) (A: edge X) (a: X)
  (Y: Type) (B: edge Y) (b: Y): Prop :=
  exists r, is_bisimulation X A Y B r /\ r a b.

Definition set_member (X: Type) (A: edge X) (a: X)
  (Y: Type) (B: edge Y) (b: Y): Prop :=
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

Proposition inl_inr_disj: forall X Y x y, inl X Y x <> inr X Y y.
intros X Y x y H.
specialize (equal_f (A := X -> Prop) (B := (Y -> Prop) -> Prop) H (fun _ => False)).
intro H0.
specialize (equal_f H0 (fun _ => True)).
unfold inl, inr.
intro H1.
rewrite H1.
exact I.
Qed.


Proposition inl_out_disj: forall X Y x, inl X Y x <> out X Y.
intros X Y x H.
specialize (equal_f (A := X -> Prop) (B := (Y -> Prop) -> Prop) H (fun _ => True)).
intro H0.
specialize (equal_f H0 (fun _ => True)).
unfold inl, out.
intro H1.
rewrite <- H1.
exact I.
Qed.

Proposition inr_out_disj: forall X Y y, inr X Y y <> out X Y.
intros X Y y H.
specialize (equal_f (A := X -> Prop) (B := (Y -> Prop) -> Prop) H (fun _ => True)).
intro H0.
specialize (equal_f H0 (fun _ => True)).
unfold inr, out.
intro H1.
rewrite <- H1.
exact I.
Qed.

Proposition inl_inj: forall X Y, injective _ _(inl X Y).
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

Proposition inr_inj: forall X Y, injective _ _ (inr X Y).
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


Definition pair_c X (A: edge X) (a: X) Y (B: edge Y) (b: Y) := sum X Y.
Definition pair_e X (A: edge X) (a: X) Y (B: edge Y) (b: Y): edge (sum X Y) := 
  fun c1 c2 =>
    (exists a1 a2, c1 = inl X Y a1 /\ c2 = inl X Y a2 /\ A a1 a2) \/
    (exists b1 b2, c1 = inr X Y b1 /\ c2 = inr X Y b2 /\ B b1 b2) \/
    (c1 = inl X Y a /\ c2 = out X Y) \/
    (c1 = inr X Y b /\ c2 = out X Y).
Definition pair_b X (A: edge X) (a: X) Y (B: edge Y) (b: Y) := out X Y.




Theorem pair_axiom:
  forall X A a Y B b Z C c, set_member Z C c (pair_c X A a Y B b) (pair_e X A a Y B b) (pair_b X A a Y B b)
    <-> set_equal Z C c X A a \/ set_equal Z C c Y B b.
split.


(* z in {x, y} -> z = x \/ z = y *)
intros H.
destruct H as [sb [H H0]].
unfold pair_b in H0.
case H0 as [H0| [H0| [H0| H0]]].

(* case 1 *)
destruct H0 as [a1 [a2 H0]].
apply False_ind.
apply (inl_out_disj X Y a2).
symmetry.
tauto.

(* case 2 *)
destruct H0 as [b1 [b2 H0]].
apply False_ind.
apply (inr_out_disj X Y b2).
symmetry.
tauto.

(* case 3 *)
destruct H0 as [H0 _].
left.

rewrite H0 in H; clear H0.
destruct H as [r [H H0]].
exists (fun z x => r z (inl X Y x)).
split; auto.
intros c1 c2 d2; split.
intros H1; destruct H1 as [H1 H2].
specialize (H c1 c2 (inl X Y d2)).
destruct H as [H H3].
destruct H as [d1 [H H4]]; auto.

assert (exists x1, d1 = inl X Y x1 /\ A x1 d2).
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

destruct H5 as [x1 [H5 H6]].
exists x1.
rewrite <- H5.
tauto.

(* bisim inv *)



(* if part *)
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

