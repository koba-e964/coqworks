Require Import Arith.

Set Implicit Arguments.

Fixpoint ack n :=
  match n with
    | 0 => S
    | S n' =>
      let fix f m :=
        match m with
          | 0 => ack n' 1
          | S m' => ack n' (f m')
        end
        in f
  end.

Fixpoint fin n : Set :=
  match n with
    | 0 => Empty_set
    | S n' => (unit + fin n')%type
  end.

Inductive prim_rec : nat -> Set :=
| pr_proj : forall n, fin n -> prim_rec n
| pr_succ : prim_rec 1
| pr_const : forall n, nat -> prim_rec n
| pr_compose :
  forall m n, (fin n -> prim_rec m) -> prim_rec n -> prim_rec m
| pr_primrec :
  forall n, prim_rec n -> prim_rec (S (S n)) -> prim_rec (S n).

Notation F0 := (inl _ tt).
Notation FS x := (inr _ x).

Definition hd n (ns : fin (S n) -> nat) := ns F0.
Definition tl n (ns : fin (S n) -> nat) := fun i => ns (FS i).

Notation "[ x , y ]" := (fun i => match i with inl _ => x | inr i' => y i' end).

Fixpoint eval n (f : prim_rec n) : (fin n -> nat) -> nat :=
  match f with
    | pr_proj n i => fun ns => ns i
    | pr_succ => fun ns => S (ns F0)
    | pr_const n k => fun _ => k
    | pr_compose m n fs g => fun ns => eval g (fun i => eval (fs i) ns)
    | pr_primrec n f g => fun ns =>
      let fix h m :=
        match m with
          | 0 => eval f (tl ns)
          | S m' => eval g [m', [h m', tl ns]]
        end
        in h (ns F0)
  end.
