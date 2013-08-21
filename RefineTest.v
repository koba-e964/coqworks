Inductive succ:nat->nat->Prop:=
succ_intro:forall n:nat,succ n (S n).


Goal forall  n:nat,~ succ n n.
intros n H.
generalize (refl_equal  n) (refl_equal  n).
pattern n at 2, n at 4 .
refine (match H in (succ s t) 
return (n=s->n=t->False)
with
|succ_intro x=> _  x
end).
intros.
refine match H0  return False with
|eq_ind => _ (_:(n=S n))
end.
apply n_Sn.
rewrite <-H0 in H1.
exact H1.
Defined.


Print le.
Goal forall n:nat,n<=0-> n=0.
intros.
generalize (refl_equal 0).
pattern 0 at 2.
info elim H.
Check le_ind.
Print le.
SearchAbout le.
Print le_ind.
info congruence.
intros.
discriminate H2.
Defined.
Require Import Bool.Bvector.



Inductive vector_in A:A->forall n,vector A n->Prop:=

|vin_head:
forall a:A,forall n:nat,forall tl:vector A n,
vector_in A a (S n) (Vcons A a n tl)
|vin_tail:
forall a b:A,forall n:nat,forall tl:vector A n,
vector_in A a (S n) (Vcons A b n tl).

Definition first:
forall (A:Type)(n:nat)(v:vector A(S n)),
{a:A|vector_in A a(S n) v}.
intros.
generalize (refl_equal (S n)).
info refine 
(match v as vv in (vector _ nn)
return (S n = nn->{a:A|vector_in A a nn vv})
with
|Vnil=>_
|Vcons a' n' v'=>_
end).
intro.
discriminate H.
intro.
exists a'.
info apply vin_tail.
Defined.

Require Import JMeq.
Definition Vcons_inv:
forall (A:Type)(n:nat)(v:vector A(S n)),
{a: A&{v':vector A n|v=Vcons A a n v'}}.
intros.
generalize(refl_equal(S n))(JMeq_refl v).
pattern (S n) at 2 ,v at 2.
info refine
(match v as vv in(vector _ n')
return (S n=n'->JMeq v vv->
{a:A&{v':vector A n|v=Vcons A a n v'}})
with
|Vnil=>_
|Vcons a' n' v'=>_
end).
discriminate.
intros H.
info injection H;clear H;intro H.
info revert v'.
info elim H.
intros.
exists a';exists v'.
rewrite H0.
auto.
Defined.


Inductive List(T:Type):nat->Type:=
|null:List T 0
|cons:forall n:nat,T->List T n->List T(S n).

Fixpoint length{n:nat}{T:Type}(lt:List T n):nat:=
match lt with
|null=>0
|cons n T lt'=>S(length lt')
end.


Definition pred{n:nat}{T:Type}(tl:List T(S n)):
List T n.
generalize (refl_equal (S n)).
pattern (S n) at 1.
refine match tl in (List _ n') return (S n=n'->List T n)
with
|null => _
|cons _ T' ltr=> _
end.
congruence.

intro.
injection H.
intros.
rewrite <-H0 in ltr.
exact ltr.
Defined.

Eval compute in pred(cons nat 0  1 (null nat:List nat 0)).


Print pred.

Definition pred2{n:nat}{T:Type}(tl:List T(S n)):
List T n.
refine ((match tl in List _ n0 return (n0=S n->List T n)with
|null=>_
|cons n0 X X0 =>_
end)(eq_refl (S n))).
discriminate.
intros.
SearchPattern( _=_->_=_).
apply eq_add_S in H.
rewrite <-H.
exact X0.
Defined.
Inductive incl{T:Type}{n:nat}(a:T):List T n->Prop
:=
|list_one:incl (n:=1)a (cons T 0 a (null _)).
|list_another :incl 







