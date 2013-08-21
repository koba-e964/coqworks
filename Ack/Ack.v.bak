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


Theorem ack_is_not_primitive_recursive :
  forall f : prim_rec 2, exists m, exists n,
    eval f (fun i => if i then m else n) <> ack m n.
Lemma wider:
forall a:nat,
forall f:prim_rec a,
exists m:nat,
forall c:nat,
m<=c->
eval f(fun i:fin a=>c)
<ack c c.
intros.
generalize (refl_equal a).
refine match f as ff in prim_rec aa
return aa = a ->
exists m : nat,
  forall c : nat,
m <= c 
-> eval ff (fun _ : fin aa => c) < ack c c
with
    | pr_proj n i => _
    | pr_succ => _
    | pr_const n k => _
    | pr_compose m n fs g => _
    | pr_primrec n f g => _
end.
intros.

simpl.
exists  1.
intros.


Admitted.
Lemma argv_equal:forall (n:nat),
forall f:prim_rec n,
forall (arg1 arg2:fin n->nat),
(forall i:fin n,arg1 i=arg2 i)->
eval f arg1=eval f arg2.
fix IHf 2.
intros n f.
generalize (refl_equal n).
refine match f as ff in prim_rec nn return nn=n->
forall arg1 arg2:fin nn->nat,(forall i : fin nn, arg1 i = arg2 i) -> eval ff arg1 = eval ff arg2
with
    | pr_proj n i => _
    | pr_succ => _
    | pr_const n k => _
    | pr_compose m n fs g => _
    | pr_primrec n f g => _
end.
simpl.
intros.
apply H0.
simpl.
intros.
rewrite H0.
auto.
simpl.
auto.
simpl.
intros.
Guarded.
apply IHf.
intro.
apply IHf.
apply H0.
Guarded.
intros.
unfold eval.
rewrite (H0 F0).
fold eval.
elim (arg2 F0).
apply (IHf _ _ (tl arg1) (tl arg2)).
unfold tl.
intro.
apply H0.
intros.
rewrite H1.
apply IHf.
intro i;case i.
auto.
intro.
fold fin in *.
case f1.
intro.
reflexivity.
intro.
apply H0.
Qed.

intros.
generalize wider.
intros.
destruct (H 2 f).
exists x.
exists x.
generalize(H0 x (le_n x));intro.
intro.
assert (forall i:fin 2,(fun _ : fin 2 => x)i=(fun i : fin 2 => if i then x else x)i).
intro.
case i;auto.
rewrite <-(argv_equal  _ _ _ H3) in H2. 
rewrite H2 in H1.
case (le_Sn_n _ H1).
Qed.