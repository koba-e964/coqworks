Require Import Arith.

Module Type SemiGroup.
  Parameter G : Type.
  Parameter mult : G -> G -> G.
  Axiom mult_assoc :
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
End SemiGroup.

Module NatMult_SemiGroup <: SemiGroup.
  Definition G := nat.
  Definition mult:= mult%nat.
  Proposition mult_assoc: 
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
    apply Nat.mul_assoc.
  Qed.
  End NatMult_SemiGroup.

Module NatMax_SemiGroup <: SemiGroup.
  Definition G := nat.
  Definition mult:= max%nat.
  Proposition mult_assoc: 
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
    apply Nat.max_assoc.
  Qed.
End NatMax_SemiGroup.

Module SemiGroup_Product (G0 G1:SemiGroup) <: SemiGroup.
  Definition G := prod G0.G G1.G.
  Definition mult x y := 
    match x with |(a1, a2) =>
      match y with |(b1, b2) => (G0.mult a1 b1, G1.mult a2 b2)
      end
    end.
  Proposition mult_assoc: 
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
  intros x y z.
  destruct x, y, z.
  unfold mult.
  rewrite G0.mult_assoc.
  rewrite G1.mult_assoc.
  reflexivity.
  Qed.
End SemiGroup_Product.
