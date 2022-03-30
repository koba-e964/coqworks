(* Hilbert-style intuitionistic calculus *)

Set Implicit Arguments.

Require Import fml.

(* H-IPC. https://en.wikipedia.org/wiki/Intuitionistic_logic *)
Inductive hipc_axiom: fml -> Set :=
  | hipc_axiom_then_1: forall a b, hipc_axiom (a ==> b ==> a)
  | hipc_axiom_then_2: forall a b c,
    hipc_axiom ((a ==> b ==> c) ==> (a ==> b) ==> a ==> c)
  | hipc_axiom_and_1: forall a b, hipc_axiom (a and b ==> a)
  | hipc_axiom_and_2: forall a b, hipc_axiom (a and b ==> b)
  | hipc_axiom_and_3: forall a b, hipc_axiom (a ==> b ==> a and b)
  | hipc_axiom_or_1: forall a b, hipc_axiom (a ==> a or b)
  | hipc_axiom_or_2: forall a b, hipc_axiom (b ==> a or b)
  | hipc_axiom_or_3: forall a b c,
    hipc_axiom ((a ==> c) ==> (b ==> c) ==> a or b ==> c)
  | hipc_axiom_false: forall a, hipc_axiom (fml_bot ==> a) 
.
Inductive hipc: fml -> Set :=
  | hipc_mp: forall {a b: fml}, hipc a -> hipc (a ==> b) -> hipc b
  | hipc_by_axiom: forall {a: fml}, hipc_axiom a -> hipc a.

(* slightly higher than  ~ (at level 75) *)
Notation "|-HIPC- s" := (hipc s) (at level 70).
