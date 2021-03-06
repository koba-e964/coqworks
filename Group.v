Require Import Relation_Definitions  Morphisms.
Require Import Setoid.
Require Import Arith.
Require Import Pnat.
Require Import MyZ.

Class Group:=
{
	T:Set;
	eq:T->T->Prop;
	e:T;
	inv:T->T;
	op:T->T->T;
	incl:T->Prop;
	equiv: Equivalence eq;
	equiv_dec:forall x y:T,{eq x y}+{~eq x y};
	closed_op:forall x y:T,incl x->incl y->incl(op x y);
closed_inv:forall x:T,incl x->incl (inv x);
incl_dec:forall x:T,{incl x}+{~incl x};
	well_inv:forall x y:T,eq x y->eq(inv x)(inv y);
	well_op:
	forall x1 y1 x2 y2:T,eq x1 y1->eq x2 y2->
	eq(op x1 x2)(op y1 y2);
well_incl:forall x1 x2:T,eq x1 x2->incl x1->incl x2;
	assoc:forall x y z:T,eq (op(op x y)z)(op x (op y z));
	e_r:forall x:T,eq(op x e)x;
	e_l:forall x:T,eq(op e x)x;
	inv_r:forall x:T,eq (op x(inv x))e;
	inv_l:forall x:T,eq(op (inv x)x)e
}.

Add Parametric Relation (G:Group): T eq
 reflexivity proved by (@Equivalence_Reflexive T  _ equiv)
 symmetry proved by (@Equivalence_Symmetric T _ equiv)
 transitivity proved by (@Equivalence_Transitive T _ equiv)
 as Group_equiv_x.

Add Parametric Morphism 
(G:Group):
inv with signature (eq==>eq)as well_inv_x.
apply well_inv.
Qed.
Add Parametric Morphism
(G:Group):
op with signature(eq==>eq==>eq)as well_op_x.
intros x y H x0 y0.
apply well_op.
exact H.
Qed.
Add Parametric Morphism 
(G:Group):
incl with signature (eq==>iff)as well_incl_x.
intros.
split.
apply well_incl.
exact H.
apply well_incl.
symmetry.
exact H.
Qed.


Theorem right_law
(g:Group)
:forall a b c:T,eq (op a c)(op b c)->eq a b.
intros.
assert (eq (op (op a c)(inv c))(op(op b c)(inv c))).
rewrite H.
reflexivity.
rewrite assoc in H0.
rewrite (assoc b c)in H0.
rewrite inv_r in H0.
rewrite e_r in H0.
rewrite e_r in H0.
exact H0.
Qed.
Theorem left_law
(g:Group)
:forall a b c:T,eq (op c a)(op c b)->eq a b.
intros.
assert (eq(op(inv c)(op c a))(op(inv c)(op c b))).
rewrite H.
reflexivity.
rewrite <-assoc in H0.
rewrite <-(assoc (inv c) c)in H0.
rewrite inv_l in H0.
rewrite e_l in H0.
rewrite e_l in H0.
exact H0.
Qed.
Theorem inv_inv(G:Group)
:forall x:T,eq (inv (inv x))x.
intros.
apply left_law  with (c:=inv x).
rewrite inv_l.
apply inv_r.
Qed.
Theorem inv_op(G:Group)
:forall x y:T,
eq(inv(op x y))(op(inv y)(inv x)).
intros.
apply right_law with (c:=(op x y)).
rewrite inv_l.
rewrite assoc.
rewrite <-(assoc(inv x)).
rewrite inv_l.
rewrite e_l.
rewrite inv_l.
reflexivity.
Qed.

Theorem inv_e(G:Group):eq(inv e)e.
apply right_law with (c:=e).
rewrite e_l.
apply inv_l.
Qed. 




Program Definition TrivialGroup:Group
:=
{|
T:=unit
;eq:=(fun a b=>True)
;e:=tt
;inv:=(fun _=>tt)
;op:=(fun _ _=>tt)
;incl:=(fun _=>True)
|}.
Obligation 1.
split.
auto.
auto.
auto.
Qed.
Obligation 2.
left.
exact I.
Qed.
Obligation 5.
left.
exact I.
Qed.


Program Definition ZGroup:Group
:=
{|
T:=myZ
;eq:=myZeq
;e:=myZzero
;inv:=myZopp
;op:=myZplus
;incl:=(fun _=>True)
;equiv:=zequiv
;well_inv:=well_myZopp
;well_op:=well_myZplus
;assoc:=myZplus_assoc
;e_r:=(fun x=>(myZplus_zero_r x))
;e_l:=(fun x=>(myZplus_zero_l x))
;inv_r:=(fun x=>(myZplus_myZopp_r x))
;inv_l:=(fun x=>(myZplus_myZopp_l x))
 |}.
Obligation 1 of ZGroup.
apply myZeq_dec.
Qed.
Obligation 4.
auto.
Qed.


Class SubGroup:Type:=
{
G:Group
;sub:T->Prop
;sub_then_incl:forall a:T,sub a->incl a
;well_sub:forall x1 x2:T,eq x1 x2->sub x1->sub x2
;op_inv_a_b:forall a b:T,sub a->sub b->sub (op (inv a)b)
;sub_e:sub e
;sub_dec:forall x:T,{sub x}+{~sub x}
}.
Add Parametric Morphism
(sg:SubGroup):
sub with signature (eq==>iff) as well_sub_x.
intros.
split.
exact (well_sub x y H).
apply (well_sub y x).
info symmetry.
exact H.
Qed.

Program Definition AsGroup(sg:SubGroup):Group:=
{|
T:=(@T G)
;incl:=sub
;eq:=eq
;e:=(@e G)
;inv:=(@inv G)
;op:=(@op G)
;equiv_dec:=(@equiv_dec (@G sg))
;incl_dec:=sub_dec
;assoc:=assoc
;e_r:=e_r
;e_l:=e_l
;inv_r:=inv_r
;inv_l:=inv_l
|}.
Obligation 1.
cut (eq x (inv(inv x))).
intro.
apply (well_sub (op(inv(inv x))y)).
rewrite <-H1.
reflexivity.
apply op_inv_a_b.
assert (sub(op (inv x)e)).
apply (op_inv_a_b x e).
exact H.
exact sub_e.
apply (well_sub  (op(inv x)e)) .
rewrite e_r.
reflexivity.
exact H2.
exact H0.
symmetry.
apply inv_inv.
Qed.
Obligation 2.
apply well_sub with (x1:=(op (inv x)e)).
apply e_r.
apply op_inv_a_b.
exact H.
exact sub_e.
Qed.
Obligation 3.
Admitted.
Obligation 4.
rewrite H.
rewrite H0.
reflexivity.
Qed.
Obligation 5.
apply (well_sub x1 x2).
exact H.
exact H0.
Qed.


Definition Normal
(sg:SubGroup):Prop
:=forall a b:T,sub (op(inv a) b)->sub(op b(inv a)).

Theorem Normal2
(sg:SubGroup)
:Normal sg
->forall a g:T,
sub a->sub (op (op (inv g)a)g).
unfold Normal.
intros.
generalize (H (inv(op a g)) (inv g)).
intros.
rewrite inv_inv in H1.
rewrite assoc in H1.
rewrite inv_r in H1.
rewrite e_r in H1.
rewrite <-assoc in H1.
apply (H1 H0).
Qed.



Class QuotientGroup:Type:=
{
sg:SubGroup
;normal_sg:Normal sg
}.
Program Definition AsQGroup(qg:QuotientGroup)
:Group:=
{|T:=(@T G)
;incl:=(@incl (@G sg))
;eq:=fun a b=>sub (op (inv a)b)
;inv:=(@inv (@G (@sg qg)))
;op:=op
;e:=e
;incl_dec:=_
|}.

Obligation 1.
split.
unfold Reflexive.
intros.
rewrite inv_l.
apply sub_e.
unfold Symmetric.
intros.
assert (sub(inv(op(inv y)x))).
rewrite inv_op.
rewrite inv_inv.
exact H.
rewrite <-(inv_inv _ (op(inv y)x)).
rewrite <-e_r.
apply op_inv_a_b.
exact H0.
exact sub_e.
unfold Transitive.
intros.

assert (sub (op(op(inv x)y)(op(inv y)z))).
apply (@closed_op (AsGroup sg) (op(inv x) y)).
exact H.
exact H0.
rewrite assoc in H1.
rewrite <-(assoc y (inv y)) in H1.
rewrite inv_r in H1.
rewrite e_l in H1.
exact H1.
Qed.
Obligation 2.
exact (sub_dec (op(inv x)y)).
Qed.
Obligation 3.
apply (closed_op x y H H0).
Qed.
Obligation 4.
apply closed_inv.
exact H.
Qed.
Obligation 5.
apply incl_dec.
Qed.
Obligation 6.
apply normal_sg.
rewrite <-inv_op.
destruct qg.
destruct sg0.
apply (@closed_inv (AsGroup sg) (op (inv x)y))  .


apply H.
Qed.

Obligation 7.
assert (sub (op(op (inv x2)(op(inv x1)y1))(op x2(op(inv x2)y2)))).
rewrite <-assoc.
generalize normal_sg.
intro.
assert (sub (op(op(inv x2)(op(inv x1)y1))x2)).
apply Normal2.
exact H1.
apply H.


apply (@closed_op (AsGroup sg) _ (op(inv x2)y2)).
exact H2.
exact H0.

rewrite inv_op.
rewrite <-(assoc x2)in H1.
rewrite inv_r in H1.
rewrite e_l in H1.
rewrite <-assoc.
rewrite (assoc _ _ y1).
exact H1.
Qed.
Obligation 8.
apply sub_then_incl in H.
assert (incl (op x1(op(inv x1)x2))).
apply (closed_op _ _ H0 H).
rewrite <-assoc in H1.
rewrite inv_r in H1.
rewrite e_l in H1.
exact H1.
Qed.

Obligation 9.
rewrite inv_op.
rewrite inv_op.
rewrite assoc.
rewrite assoc.
rewrite <-(assoc (inv x)x).
rewrite inv_l.
rewrite e_l.
rewrite <-(assoc(inv y)).
rewrite inv_l.
rewrite e_l.
rewrite inv_l.
apply sub_e.
Qed.
Obligation 10.
rewrite e_r.
rewrite inv_l.
apply sub_e.
Qed.

Obligation 11.
rewrite e_l.
rewrite inv_l.
exact sub_e.
Qed.
Obligation 12.
rewrite inv_r.
rewrite inv_l.
exact sub_e.
Qed.
Obligation 13.
rewrite inv_l.
rewrite inv_l.
exact sub_e.
Qed.

Program Definition nMyZ(n:nat):SubGroup
:=
{|
G:=ZGroup
;sub:=fun k:myZ=>(exists m:myZ,k==(myZpos n)*m)
;sub_then_incl:=_
;well_sub:=_
;op_inv_a_b:=_
;sub_e:=_
;sub_dec:=_
|}.
Obligation 2.
destruct x1,x2,H0.
rewrite H in H1.
exists (myZmake n4 n5).
apply H1.
Qed.

Obligation 3.
exists ((myZopp H)+H0).
rewrite H1.
rewrite H2.
change (myZopp
  ((myZpos n)*H)+
  ((myZpos n)*H0)
==((myZpos n)*(myZopp H + H0))).
rewrite <-myZmul_myZopp_compat_r.
symmetry.
apply myZmul_myZplus_distr_l.
Qed.
Obligation 4.
change(exists m : myZ,
myZzero==(myZpos n)*m
).
exists myZzero.
simpl.
ring.
Qed.
Obligation 5.
change({(exists m : myZ,x ==(myZpos n)*m)} +
{~(exists m : myZ,x ==(myZpos n)*m)}).
apply myZdivisible_dec.
