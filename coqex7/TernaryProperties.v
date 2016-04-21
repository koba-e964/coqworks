Require Import Ternary.

Lemma andt_assoc a b c : (a && (b && c) = (a && b) && c)%tern.
Proof.
  destruct a; destruct b; destruct c; reflexivity.
Qed.
