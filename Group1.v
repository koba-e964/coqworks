Require Import Setoid.

Module Type Group.

Parameter S:Type.
Parameter opT:S->S->S.
Parameter s0:S.
Parameter eqT:S->S->Prop.
Parameter inclT:S->Prop.
Infix "/":=opT.
Definition e:S:=s0/s0.

Hypothesis unit:forall a:S,eqT (a/a) e.
Hypothesis eqT_dec:forall a b:S,{eqT a b}+{~eqT a b}.
Hypothesis inclT_dec:forall a:S,{inclT a}+{~inclT a}.
Hypothesis equiv_eqT:Equivalence eqT.
Hypothesis well_opT:forall a1 a2 b1 b2:S,
eqT a1 a2->eqT b1 b2->eqT(a1/b1)(a2/b2).
Hypothesis closed_opT:forall a b:S,
inclT a->inclT b->inclT (a/b).
Hypothesis well_inclT:forall a b:S,
eqT a b->if inclT_dec a then inclT b else ~inclT b.
Infix "==":=eqT (at level 70,no associativity).
Hypothesis ga0:forall a:S,a/e==a.
Hypothesis ga1:forall b c:S,e/(b/c)==c/b.
Hypothesis ga2:forall a b c:S,(a/c)/(b/c)==a/b.
End Group.
Module GroupProperty(Gr:Group).
Include Gr.
Definition inv(a:S):S:=e/a.
Definition mult(a b:S):S:=a/(inv b).
Infix "*":=mult.
Add Parametric Relation:S eqT
reflexivity proved by (@Equivalence_Reflexive S eqT equiv_eqT)
symmetry proved by (@Equivalence_Symmetric S eqT equiv_eqT)
transitivity proved by(@Equivalence_Transitive S eqT equiv_eqT)
as eqT_equivalence.
Add Parametric Morphism :opT with signature(eqT==>eqT==>eqT)
as opT_well_defined.
intros.
apply well_opT.
exact H.
exact H0.
Qed.

Theorem well_inclT_iff:forall a b:S,
eqT a b->(inclT a<->inclT b).
intros.
split.
intros.
generalize (well_inclT a b H).
intros.
case (inclT_dec a) in *.
apply H1.
case (n H0).
info symmetry in H.
generalize (well_inclT b a H).
case (inclT_dec b).
auto.
tauto.
Qed.

Add Parametric Morphism:inclT
with signature (eqT==>iff)
as inclT_well_defined.
exact well_inclT_iff.
Qed.




Theorem mul_s_inv:forall s:S,
s*inv s==e.
intros.
unfold mult.
unfold inv.
rewrite ga1.
rewrite ga0.
apply unit.
Qed.


Theorem mul_inv_s:forall s:S,
(inv s)*s==e.
intros.
apply unit.
Qed.

Theorem mul_e_s:forall s:S,
e*s==s.
unfold mult.
unfold inv.
intros.
rewrite ga1.
apply ga0.
Qed.
Theorem mul_s_e:forall s:S,
s*e==s.
intros.
unfold mult.
unfold inv.
rewrite unit.
apply ga0.
Qed.


Lemma inv_inv_s:forall s:S,
inv (inv s)==s.
intro.
unfold inv.
rewrite ga1.
apply ga0.
Qed.
Lemma mult_op:forall a b:S,
(a*b)/b==a.
intros.
unfold mult.
cut (a/inv b/b==a/(e/b)/(inv (inv b))).
intros.
rewrite H.
unfold inv.
rewrite ga2.
exact (ga0 a).
rewrite inv_inv_s.
reflexivity.
Qed.



Theorem assoc:forall a b c:S,
a*(b*c)==(a*b)*c.
intros.
unfold mult.
unfold inv.


rewrite ga1.
rewrite <-(ga2 (a/(e/b))  (e/c) b).
assert (a==a/(e/b)/b).
cut (a/(e/b)==a*b).
intros.

rewrite H.
symmetry;apply (mult_op a b).
unfold mult,inv;reflexivity.
rewrite <-H.
reflexivity.
Qed.

End GroupProperty.

Add Parametric Relation(G:Group):S eqT
reflexivity proved by (@Equivalence_Reflexive S eqT equiv_eqT)
symmetry proved by (@Equivalence_Symmetric S eqT equiv_eqT)
transitivity proved by(@Equivalence_Transitive S eqT equiv_eqT)
as eqT_equivalence.
Add Parametric Morphism :opT with signature(eqT==>eqT==>eqT)
as opT_well_defined.
intros.
apply well_opT.
exact H.
exact H0.
Qed.
Add Parametric Morphism:inclT
with signature (eqT==>iff)
as inclT_well_defined.
exact well_inclT_iff.
Qed.


Module Type SubGroup(G:Group)<:Group.
Definition S:Type:=G.S.
Parameter (subT:S->Prop).
Definition inclT:=subT.
Hypothesis subT_then_inclT:
forall a:S,
subT a->G.inclT a.
Parameter (subT_dec:forall s:S,{subT s}+{~subT s}).
Definition opT:=G.opT.
Parameter (subT_closed_opT:forall a b:S,subT a->subT b->
subT (opT a b)).
Definition eqT:=G.eqT.
Parameter well_subT:
forall a b:S,
eqT a b->if subT_dec a then subT b else ~subT b.
Definition s0:=G.e.
Definition e:=opT s0 s0.
Definition unit:forall a:S,eqT(opT a a)e.
intro.
rewrite G.unit.
symmetry.
unfold e.
apply G.unit.
Qed.
Definition eqT_dec:forall a b:S,{eqT a b}+{~eqT a b}:=G.eqT_dec.
Definition inclT_dec:forall a:S,{inclT a}+{~inclT a}:=subT_dec.
Definition equiv_eqT:Equivalence eqT:=G.equiv_eqT.
Infix "/":=opT.
Definition well_opT:forall a1 a2 b1 b2:S,
eqT a1 a2->eqT b1 b2->eqT(a1/b1)(a2/b2):=G.well_opT.
Definition closed_opT:forall a b:S,
inclT a->inclT b->inclT (a/b):=subT_closed_opT.
Definition well_inclT:forall a b:S,
eqT a b->if inclT_dec a then inclT b else ~inclT b.
apply well_subT.
Qed.
Infix "==":=eqT (at level 70,no associativity).
Definition ga0:forall a:S,a/e==a.
intro.
unfold e.
repeat rewrite G.ga0.
reflexivity.
Qed.
Definition ga1:forall b c:S,e/(b/c)==c/b.
intros.
unfold e.
rewrite G.ga0.
rewrite G.ga1.
reflexivity.
Qed.
Definition ga2:forall a b c:S,(a/c)/(b/c)==a/b:=G.ga2.
Definition inv(s:S):=opT e s.
Definition mult(a b:S):=a/(inv b).
Add Parametric Relation:S eqT
reflexivity proved by (@Equivalence_Reflexive S eqT equiv_eqT)
symmetry proved by (@Equivalence_Symmetric S eqT equiv_eqT)
transitivity proved by(@Equivalence_Transitive S eqT equiv_eqT)
as eqT_equivalence.
Add Parametric Morphism :opT with signature(eqT==>eqT==>eqT)
as opT_well_defined.
intros.
apply well_opT.
exact H.
exact H0.
Qed.
Theorem well_inclT_iff:forall a b:S,
eqT a b->(inclT a<->inclT b).
intros.
split.
intros.
generalize (well_inclT a b H).
intros.
case (inclT_dec a) in *.
apply H1.
case (n H0).
info symmetry in H.
generalize (well_inclT b a H).
case (inclT_dec b).
auto.
tauto.
Qed.
Add Parametric Morphism:inclT
with signature (eqT==>iff)
as inclT_well_defined.
exact well_inclT_iff.
Qed.
Infix "*":=mult.
Theorem mul_s_inv:forall s:S,
s*inv s==e.
intro.
unfold mult.
unfold inv.
rewrite ga1.
rewrite ga0.
apply unit.
Qed.


Theorem mul_inv_s:forall s:S,
(inv s)*s==e.
intros.
apply unit.
Qed.

Theorem mul_e_s:forall s:S,
e*s==s.
unfold mult.
unfold inv.
intros.
rewrite ga1.
apply ga0.
Qed.
Theorem mul_s_e:forall s:S,
s*e==s.
intros.
unfold mult.
unfold inv.
rewrite unit.
apply ga0.
Qed.


Lemma inv_inv_s:forall s:S,
inv (inv s)==s.
intro.
unfold inv.
rewrite ga1.
apply ga0.
Qed.
Lemma mult_op:forall a b:S,
(a*b)/b==a.
intros.
unfold mult.
cut (a/inv b/b==a/(e/b)/(inv (inv b))).
intros.
rewrite H.
unfold inv.
rewrite ga2.
exact (ga0 a).
rewrite inv_inv_s.
reflexivity.
Qed.



Theorem assoc:forall a b c:S,
a*(b*c)==(a*b)*c.
intros.
unfold mult.
unfold inv.


rewrite ga1.
rewrite <-(ga2 (a/(e/b))  (e/c) b).
assert (a==a/(e/b)/b).
cut (a/(e/b)==a*b).
intros.

rewrite H.
symmetry;apply (mult_op a b).
unfold mult,inv;reflexivity.
rewrite <-H.
reflexivity.
Qed.

End SubGroup.
