Require Import QArith.
Require Import ZArith.

Inductive Poly:Set:=
|zero:Poly
|indinc:Poly->Q->Poly.
Module Exp.
Definition x:=indinc (indinc zero 1) 0.

Fixpoint PAdd(a b:Poly):Poly:=
match a with
|zero => b
|indinc  a1 a2=>
(fix PAdd2 (a1:Poly)(a2:Q)(b:Poly):Poly:= 
match b with
|zero => indinc a1 a2
|indinc b1 b2=>indinc (PAdd a1 b1) (a2+b2)
end
)a1 a2 b
end.
Infix "+" :=PAdd.

Fixpoint xPwr(n:nat):Poly:=
match n with
|O => indinc zero 1
|S n'=> indinc (xPwr n') 0
end.
Fixpoint QPMul(a2:Q)(b:Poly):Poly:=
match b with
|zero => zero
|indinc b1 b2=> indinc (QPMul a2 b1) (a2*b2)
end.
Fixpoint PMul(a b:Poly):Poly:=
match a with
|zero => zero
|indinc a1 a2=>(indinc (PMul a1 b) 0)+
QPMul a2 b
end. 

Infix "*":=PMul.


Definition PQAdd(a:Poly)(b:Q):Poly:=a+(indinc 
zero b).

Definition QPAdd(b:Q)(a:Poly):Poly:=a+(indinc 
zero b).



Fixpoint PPower(a:Poly)(n:nat):Poly:=
match n with
|O=> indinc zero 1
|S n'=> PMul a(PPower a n')
end.
Infix "^":=PPower.

Require Import Ring.

Fixpoint PDegP1(a:Poly):nat:=
match a with
|zero=>0%nat
|indinc a' c =>
let r:=PDegP1 a' in
match r with
|O=>(if (Qeq_bool c 0) then O else S O)
|S _=> S r
end end.
Eval compute in PDegP1 ((indinc zero 0)).


Fixpoint PSubst(a:Poly)(b:Q):Q:=
match a with
|zero=>0%Q
|indinc a' c=>Qplus (Qmult b(PSubst a' b)) c%Q
end.

Fixpoint PMonic(a:Poly):bool:=
match a with
|zero=>false
|indinc a' c=>
match a' with|zero=>(Qeq_bool c 1)|indinc _ _=>PMonic a'
end end.
Fixpoint PTop(a:Poly):Q:=
match a with
|zero=>0%Q
|indinc a' _=>PTop a'
end.

Definition QNot0:Set:={x:Q|~x==0}.

Inductive PolyDeg:Set:=
|null:PolyDeg
|top:QNot0->PolyDeg
|indpq:PolyDeg->Q->PolyDeg.

Definition MakeQNot0(q:Q)(pr:~q==0):QNot0.
exists q.
apply pr.
Qed.
Definition QNot0ToQ(a:QNot0):Q.
destruct a.
apply x0.
Qed.
Require Import Pnat.

Theorem Tmp0:forall p:Poly,
(beq_nat (PDegP1 p) 1%nat)=true->exists p2:Poly,exists p3:Q,
p=indinc p2 p3 /\ ~ p3==0.
destruct p as[|pover q].
intro.
simpl in H.
apply False_ind.
apply diff_false_true.
auto.
simpl.
intros.
assert (~q==0).
apply beq_nat_true in H.
apply Qeq_bool_neq.
assert (forall b:bool,(if b then 0%nat else 1%nat)=1%nat->b=false).
destruct b. intro;auto. apply O_S in H0.
apply False_ind;apply H0.
intro;auto.
assert (forall i:nat,forall b:bool,
match i with|O=> if b then O else 1%nat|S _=> S i end =1%nat->i=0%nat/\b=false).
intros i b.
elim i.
split;auto;apply H0.
intros.
symmetry in H2. apply eq_add_S in H2. apply O_S in H2.
apply False_ind;auto.
apply H1 with (b:=Qeq_bool q 0) in H.
apply H.
exists pover;exists q.
auto.
Qed.

Eval compute in ~1%Q==0%Q.

Definition NullQNot0:QNot0.
apply (fun i=>MakeQNot0 1 i).
compute.
intro.
apply Zeq_is_eq_bool in H.
compute in H.
apply diff_false_true;auto.
Qed.


Definition Tmp1(a:Poly):QNot0:=
let r:=PDegP1 a in
match r with
|O=>NullQNot0
|S O=>
match a with 
|zero=>NullQNot0
|indinc a' c=>
MakeQNot0 c (Tmp0)
end end.


Fixpoint PolyToPolyDeg(a:Poly):PolyDeg.


case (PDegP1 a).
apply null.
intros b inter.
elim a.
apply null.
intros b1  inter2 b2.
elim b.
apply top.
apply (fun i=>MakeQNot0 b2 i).
apply Tmp0.
apply (top (MakeQNot0 b2 )).
|S r'=> indpq(tmp0 a1 r')a2
end end).
end.




Fixpoint PRem(a b:Poly):Poly:=
match b with
|zero=>a
|indinc b' c=>
(if (PDeg a>=PDeg b) 
end.





