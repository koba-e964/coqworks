(* Prove some properties of System F by dinaturality axiom 
  with Coq's internal type system.
  System F's type is encoded as a Prop. *)
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



