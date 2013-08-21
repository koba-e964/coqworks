Require Import Arith.
Require Import Coq.Logic.JMeq.
Inductive fin:nat->Type:=
|car:forall m,fin m 
|cdr:forall m:nat,fin m->fin(S m).
Program Fixpoint getfin(i n:nat):fin n:=
match n as x with
|0=>car n
|S n'=>match i with
|0=>car n
|S i'=>cdr _ (getfin i' n')
end end.

Definition cons n(i0:nat)(rest:fin n->nat):fin (S n)->nat.
intro.
generalize (refl_equal (S n)).
pattern n at 2.
refine match H in (fin k)
return (S n=k->nat)
with
|car Sn=>(fun _ _=>i0) Sn
|cdr n0 rest'=> _ n0
end.
intros.
SearchPattern (S _=S _->_=_).
apply eq_add_S in H0.
rewrite <-H0 in rest'.
exact (rest rest').
Defined.

Definition nil(_:fin 0):nat:=0.

Notation "[ a , b ]" := (cons _ a b).

Eval compute in getfin 3 4.
Inductive Recu:nat->Type:=
|add:Recu 2
|mul:Recu 2
|proj:forall k,fin k->Recu k
|equal:Recu 2
|synth:forall n:nat,forall m:nat,(fin n->Recu m)->Recu n->Recu m
|mu:forall n:nat,forall con:nat->fin n->Prop,forall argv:fin n,(exists b:nat,con b argv)->Recu n.
Definition nth n(argv:fin n->nat)(i:nat):nat
:=
if negb(leb i n) then argv (getfin i n) else 0.

Notation "a [ b ]":=(nth _ a b) (at level 200).

Definition eqtest m n(H:m=n)(i:fin m->nat):fin n->nat.
rewrite <-H.
exact i.
Defined.
Print eqtest.
Print eq_rec.


Program Fixpoint eval n (f:Recu n)(a:fin n->nat):nat:=
match f with
|add=>((nth _ a 0) + (nth _ a 1))
|mul=>((nth _ a 0) * (nth _ a 1))
|proj k ind=>a _
|equal=> if(beq_nat (nth _ a 0)(nth _ a 1)) then 1 else 0
|synth k n funcs g=> eval k g (fun i:fin k=>eval n ( funcs i) (eqtest _ _ _ a)) 
|mu n con argv proof=> match proof  as H with 
|ex_intro x H00=>
((fix tmp0(y:nat):nat:=
match y with
|0=>x
|S y'=>if (negb (leb x (x-y)))
then x-y else tmp0 y' end)x)
end
end.
Obligation 1.
apply ind.
Defined.



