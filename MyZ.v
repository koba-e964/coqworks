Require Import Relation_Definitions  Morphisms.
Require Import Setoid.
Require Import Arith.
Require Import Pnat.
Require Import Setoid.

Inductive myZ:Set:=
myZmake:nat->nat->myZ.
Module MyZ.

Definition myZeq(z1:myZ)(z2:myZ):Prop:=
match z1 with myZmake x1 y1=>
match z2 with myZmake x2 y2=>
x1+y2=y1+x2
end end.
Definition myZplus(z1 z2:myZ):myZ:=
match z1 with myZmake x1 y1=>
match z2 with myZmake x2 y2=>
myZmake (x1+x2)(y1+y2)
end end.
Definition myZopp(z:myZ):myZ:=
match z with myZmake x y=>myZmake y x end.

Definition myZzero:myZ:=myZmake 0 0.

Theorem zequiv:Equivalence myZeq.
split.
unfold Reflexive.
intro.
induction x.
simpl.
apply plus_comm.
unfold Symmetric.
unfold myZeq.
 induction x. 
induction y .
simpl.
intros.
rewrite plus_comm.
rewrite (plus_comm n2 n).
symmetry.
apply H.
unfold Transitive.
induction x.
induction y.
induction z.
simpl.
intros.

apply plus_reg_l with (p:=n1+n2).
rewrite plus_permute_2_in_4 with (p:=n0).
rewrite <-H0.
rewrite (plus_comm n1 n0).
rewrite <-H.
rewrite (plus_comm n n2).
rewrite (plus_comm n1 n2).
apply plus_permute_2_in_4.
Qed.
Infix "+":=myZplus.
Infix "==":=myZeq (at level 70).
Theorem myZplus_zero:forall z:myZ,z+myZzero==z/\myZzero+z==z.
induction z.
simpl.
rewrite plus_0_r.
rewrite plus_0_r.
rewrite plus_comm.
auto.
Qed.
Theorem myZplus_inv:forall z:myZ,z+myZopp z==myZzero/\(myZopp z)+z==myZzero.
induction z.
simpl.
rewrite plus_0_r.
rewrite plus_0_r.
rewrite plus_comm.
auto.
Qed.
Theorem myZplus_assoc:forall a b c:myZ,(a+b)+c==a+(b+c).
induction a.
induction b.
induction c.
simpl.
rewrite <-(plus_assoc n n1 n3).
rewrite <-(plus_assoc n0 n2 n4).
apply plus_comm.
Qed.
Theorem myZplus_comm:forall a b:myZ,a+b==b+a.
induction a.
induction b.
simpl.
ring.
Qed.


Theorem well_myZplus:forall a1 a2 b1 b2:myZ,
a1==a2->b1==b2->(a1+b1)==(a2+b2).
induction a1;induction a2;induction b1;induction b2.
simpl.
intros.
rewrite plus_permute_2_in_4.
rewrite plus_permute_2_in_4 with (p:=n1).
rewrite H;rewrite H0.
auto.
Qed.

Theorem well_myZopp:forall z1 z2:myZ,
z1==z2->myZopp z1==myZopp z2.
induction z1;induction z2.
simpl.
intro;auto.
Qed.

Theorem myZeq_dec:forall x y:myZ,{x==y}+{~(x==y)}.
induction x.
induction y.
simpl.
apply eq_nat_dec.
Qed.



Definition myZmul(z1 z2:myZ):myZ:=
match z1 with myZmake x1 y1=>
match z2 with myZmake x2 y2=>
myZmake (x1*x2+y1*y2)(x1*y2+x2*y1)
end end.
Definition myZsub(a b:myZ):myZ:=a+(myZopp b).
Infix "*":=myZmul.
Infix "-":=myZsub.
Definition myZdivisor (z1 z2:myZ):Prop:=
exists a:myZ,z1*a==z2.
Infix "|||":=myZdivisor (at level 90).
Definition myZmod (mod a b:myZ):Prop:=
mod ||| (a-b).
Definition myZpos(n:nat):myZ:=myZmake n 0.
Definition myZneg(n:nat):myZ:=myZmake 0 n.
Goal myZmod (myZpos 4) (myZpos 5)(myZpos 1).
unfold myZmod.
unfold myZdivisor.
exists (myZmake 1 0).
simpl.
reflexivity.
Qed.
Definition myZlt(z1 z2:myZ):Prop:=
match z1 with myZmake x1 y1=>
match z2 with myZmake x2 y2=>
x1+y2<y1+x2
end end.
Infix "<":=myZlt.
Definition myZmul_comm:forall a b:myZ,
a*b==b*a.
induction a;induction b.
simpl.
ring.
Qed.

Definition myZmul_assoc:forall a b c:myZ,
(a*b)*c==a*(b*c).
induction a;induction b;induction c.
simpl.
ring.
Qed.
Add Parametric Relation : myZ myZeq
 reflexivity proved by (@Equivalence_Reflexive myZ  _ zequiv)
 symmetry proved by (@Equivalence_Symmetric myZ _ zequiv)
 transitivity proved by (@Equivalence_Transitive myZ _ zequiv)
as myZequiv.
Add Parametric Morphism :
myZplus with signature (myZeq==>myZeq==>myZeq)as well_myZplus_x.
intros.
apply well_myZplus;
auto.
Qed.
Add Parametric Morphism :
myZmul with signature (myZeq==>myZeq==>myZeq)as well_myZmul_x.
induction x.
induction y.
intro H.
induction x0.
induction y0.
simpl in *.
intro.
apply (plus_reg_l _ _(n5*n)).
Open Scope nat_scope.
assert  (n5 * n + (n * n3 + n0 * n4 + (n1 * n6 + n5 * n2))=n*n3+n0*n4+n1*n6+(n5*(n+n2))).
ring.
rewrite H1.
rewrite H.
assert (n * n3 + n0 * n4 + n1 * n6 + n5 * (n0 + n1) 
=n * n3 + n0 * (n4+n5) + n1 * n6 + n5 *  n1 ).
ring.
rewrite H2.
rewrite <-H0.
assert (n5 * n + (n * n4 + n3 * n0 + (n1 * n5 + n2 * n6))
=n * (n4+n5) + n3 * n0 + (n1 * n5 + n2 * n6)).
ring.
rewrite H3.
rewrite<-H0.
assert(n * (n3 + n6) + n3 * n0 + (n1 * n5 + n2 * n6)
=n * n3  + n3 * n0 + n1 * n5+(n+n2)*n6 ).
ring.
rewrite H4.
rewrite H.
ring.
Close Scope nat_scope.
Qed.

Add Parametric Morphism :
myZlt with signature (myZeq==>myZeq==>iff)as well_myZlt_x.

intros.
destruct x,y,x0,y0.
simpl in *.
split.
intro.
apply (plus_le_reg_l _ _ n3).
rewrite<-plus_n_Sm.
rewrite plus_assoc.
rewrite plus_comm.
rewrite plus_assoc.
rewrite (plus_comm n6).
rewrite H0.

rewrite H0.


Theorem myZmul_myZplus_distr_r:forall n m p : myZ, (n + m) * p == n * p + m * p.
induction n.
induction m.
induction p.
simpl.
ring.
Qed.

Theorem myZmul_myZplus_distr_l:forall n m p : myZ, n *(m+p) == n * m + n * p.
induction n.
induction m.
induction p.
simpl.
ring.
Qed.

Theorem myZdivisor_additive:
forall n m p:myZ,
n|||m->n|||p->n|||m+p.
intros.
destruct H,H0.
exists (x+x0).
rewrite myZmul_myZplus_distr_l.
rewrite H,H0.
reflexivity.
Qed.
Theorem myZdivisor_multiplicative:
forall n m p:myZ,
n|||m->n|||m*p.
intros.
destruct H.
exists (x*p).
rewrite <-myZmul_assoc.
rewrite H.
reflexivity.
Qed.
(* bool functions*)
Definition myZbeq(a b:myZ):bool:=
match a with myZmake x y=>
match b with myZmake z w=>
beq_nat (x+w)(y+z)end end.

Theorem myZbeq_true:
forall a b:myZ,
myZbeq a b=true->a==b.
intros.
destruct a,b.
apply beq_nat_true in H.
apply H.
Qed.
Theorem myZbeq_true_iff:
forall a b:myZ,
myZbeq a b=true<->a==b.
intros a b.
split.
apply myZbeq_true.
destruct a,b.
simpl.
intro H.
rewrite H.
symmetry.
apply beq_nat_refl.
Qed.

Definition myZblt(a b:myZ):bool:=
match a with myZmake x y=>
match b with myZmake z w=>
leb (S(x+w))(y+z) end end.

Theorem myZblt_true:
forall a b:myZ,
myZblt a b=true->a<b.
intros.
destruct a,b.
unfold myZblt in H.
simpl.
apply leb_complete in H.
apply H.
Qed.

Theorem myZblt_true_iff:
forall a b:myZ,
myZblt a b=true<->a<b.
intros a b.
split.
apply myZblt_true.
intros.
SearchAbout leb.
destruct a,b.
simpl in H.
apply leb_correct.
apply H.
Qed.

Theorem myZplus_order:
forall m n p:myZ,
m<n->m+p<n+p.
intros.
destruct m,n,p.
simpl in *.
assert (n0 + n3 + (n2 + n4)
=n3+n4+(n0+n2))%nat.
ring.
assert (n1 + n4 + (n + n3)
=n3+n4+(n1+n))%nat.
ring.
rewrite H0,H1.
unfold lt.
rewrite plus_n_Sm.
apply plus_le_compat.
apply le_n.
exact H.
Qed.
Theorem myZlt_trans:
forall m n p:myZ,
m<n->n<p->m<p.
intros.
destruct m,n,p.
simpl in *.
SearchPattern (_<=_->_<=_)%nat.
apply (plus_le_reg_l _ _ (n+n2)).
rewrite <-plus_n_Sm.
assert (n+n2+(n1+n3)=n1+n+(n2+n3))%nat.
ring.
rewrite  H1.
assert ((n + n2 + (n0 + n4))=n0+n2+(n+n4))%nat.
ring.
rewrite H2.
apply plus_lt_compat.
apply H.
apply H0.
Qed.

Theorem myZplus_myZlt_compat:
forall a b c d:myZ,
a<b->c<d->a+c<b+d.
intros.
apply (myZlt_trans _ (b+c)).
apply myZplus_order.
exact H.
rewrite (myZplus_comm xx).


Theorem myZmul_pos_order:
forall m n p:myZ,
myZzero<p->m<n->m*p<n*p.
intros.



End MyZ.
