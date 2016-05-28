(* Prove some properties of System F by dinaturality axiom 
  with Coq's internal type system.
  System F's type is encoded as a Prop. *)

(* According to
  A Logic for Parametric Polymorphism, Plotkin and Abadi (LNCS 1993),
  which introduces dinaturality as an axiom.
*)
Require Import Coq.Logic.FunctionalExtensionality.


Definition one := forall (X: Prop), (X -> X).

Definition compose {X Y Z} (f: Y -> Z) g (x: X) := f (g x).

Axiom dinaturality0one:
  forall (X Y: Prop) (f: X -> Y), forall (u: one),
  compose f (u X) = compose (u Y) f.

Theorem one_singleton:
  forall u: one, u = id.
intro u.
apply functional_extensionality_dep.
intro X.
apply functional_extensionality.
intro x.
generalize (dinaturality0one one X (fun _ => x) u); intro H.
unfold compose in H.
apply equal_f in H.
symmetry.
auto.
exact id.
Qed.

Definition prod (X: Prop) (Y: Prop): Prop :=
  forall Z: Prop, (X -> Y -> Z) -> Z.

Axiom dinaturality0Prod:
  forall (X Y Z Z': Prop) (f: Z -> Z') (u: prod X Y),
  compose f (u Z) = fun g => u Z' (fun x y => f (g x y)).

Definition pair {X Y: Prop} (x: X) (y: Y): prod X Y :=
  fun _ f => f x y.

Definition fst {X Y: Prop} (p: prod X Y): X :=
  p X (fun x _ => x).

Definition snd {X Y: Prop} (p: prod X Y): Y :=
  p Y (fun _ y => y).

Lemma p_pair: forall X Y (p: prod X Y), p _ pair = p.
Admitted.

Theorem prod_ok:
  forall X Y (p: prod X Y), p = pair (fst p) (snd p).
intros X Y p.
apply functional_extensionality_dep; intro Z.
apply functional_extensionality; intro q.
unfold pair.
generalize (dinaturality0Prod X Y (prod X Y) Z (fun r => q (fst r) (snd r)) p); intro H.
unfold compose in H.
generalize (equal_f H pair); intro H0.
repeat rewrite (p_pair _ _ p) in H0.
rewrite H0.
unfold fst, snd, pair.
reflexivity.
Qed.
