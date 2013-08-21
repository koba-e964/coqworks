Require Import Relations.
Require Import Setoid.

(* Module is a mere abelian group,with operation add,neg. *)

Class Module
{T:Set}
(eqT:T->T->Prop)
(addT:T->T->T)
(negT:T->T)
(zeroT:T)
:=
{
equivT:Equivalence eqT
;well_addT:forall a1 a2 b1 b2:T,
eqT a1 a2->eqT b1 b2->
eqT(addT a1 b1)(addT a2 b2)
;well_negT:forall a1 a2:T,
eqT a1 a2->eqT(negT a1)(negT a2)
;comm_addT:forall a b:T,
eqT(addT a b)(addT b a)
;add_0:forall a:T,
eqT(addT a zeroT)a
;add_neg:forall a:T,
eqT(addT a (negT a))zeroT
;assoc_addT:forall a b c:T,
eqT (addT(addT a b)c)(addT a (addT b c))
}.

Print Equivalence.
Print Equivalence_Reflexive.
Print Reflexive.
Add Parametric Relation
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
(Mod:Module eqT addT negT zeroT):
T (eqT:T->T->Prop)
 reflexivity proved by (@Equivalence_Reflexive _ _ equivT)
 symmetry proved by (@Equivalence_Symmetric _ _ equivT)
 transitivity proved by (@Equivalence_Transitive _ _ equivT)
 as T_setoid.


Record Morph
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
(MA:Module eqA addA negA zeroA)
(MB:Module eqB addB negB zeroB):=
mkMorph
{
func:TA->TB
;map_0:eqB (func zeroA)zeroB
;map_hom_add:forall a1 a2:TA,
eqB(func (addA a1 a2))
(addB (func a1)(func a2))
;map_hom_neg:forall a:TA,
eqB (func (negA a))(negB(func a))
;well_morph:forall a1 a2:TA,
eqA a1 a2->eqB (func a1)(func a2)
}.
Add Parametric Morphism
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
(Mod:Module eqT addT negT zeroT):
addT with signature (eqT==>eqT==>eqT) as well_addT_x.
intros.
apply well_addT.
exact H.
exact H0.
Qed.
Add Parametric Morphism
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
(MOd:Module eqT addT negT zeroT):
negT with signature (eqT==>eqT) as well_negT_x.
exact well_negT.
Qed.



Module ModTheo.

Theorem neg_zero
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
(Mod:Module eqT addT negT zeroT)
:eqT(negT zeroT)zeroT.
rewrite <-(add_0 (negT zeroT)).
rewrite comm_addT.
exact (add_neg zeroT).
Qed.

Theorem rm_common
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
:forall Mod:Module eqT addT negT zeroT,
forall a b c:T,
eqT (addT b a)(addT c a)->eqT b c.
intros.
assert (forall x:T,eqT x (addT (addT x a)(negT a))).
intros.
rewrite assoc_addT.
rewrite add_neg. 
rewrite add_0.
reflexivity.
rewrite (H0 b).
rewrite (H0 c).
rewrite H.
reflexivity.
Qed.

Add Parametric Morphism
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f:Morph MA MB):
(func MA MB f) with signature (eqA==>eqB) as well_morph_x.
intros.
apply well_morph.
exact H.
Qed.

Theorem swap_2_in_4
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
{Mod:Module eqT addT negT zeroT}
:forall a b c d:T,
eqT (addT (addT a b)(addT c d))
(addT (addT a c)(addT b d)).
intros.
rewrite assoc_addT.
rewrite <-(assoc_addT b).
rewrite (comm_addT b c).
rewrite assoc_addT.
rewrite <-(assoc_addT a).
reflexivity.
Qed.


End ModTheo.



Definition ZeroMorph
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
(MA:Module eqA addA negA zeroA)
(MB:Module eqB addB negB zeroB):
Morph MA MB
:=
{|
func := fun _ : TA => zeroB;
map_0 := reflexivity zeroB;
map_hom_add := fun _ _ : TA =>
               Morphisms.trans_sym_co_inv_impl_morphism
                 (Equivalence_PER (T_setoid MB)) (addB zeroB zeroB) zeroB
                 (add_0 zeroB) (reflexivity zeroB);
map_hom_neg := fun _ : TA =>
               symmetry (x:=negB zeroB) (y:=zeroB) (ModTheo.neg_zero MB);
well_morph := fun (a1 a2 : TA) (_ : eqA a1 a2) => reflexivity zeroB |}.


Definition EqualMorph
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f g:Morph MA MB):Prop:=
forall a:TA,
eqB (func MA MB f a)
(func MA MB g a).



Theorem EquivMorph
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
:Equivalence EqualMorph.
split.
unfold Reflexive;intros;
unfold EqualMorph;
intros;reflexivity.
unfold Symmetric;unfold EqualMorph.
intros.
symmetry;apply H.
unfold Transitive;unfold EqualMorph.
intros.
rewrite H.
apply H0.
Qed.

Definition monomorph

{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f:Morph MA MB)
:Prop:=
forall a:TA,
eqB (func MA MB f a)zeroB
->eqA a zeroA.
Theorem monomorph_variant
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f:Morph MA MB)
:monomorph f<->
(forall a t:TA,
eqB (func MA MB f t)(func MA MB f a)
<->eqA t a).
split.
intros.
split;intro.

apply (ModTheo.rm_common MA(negA a)).
rewrite add_neg.
apply H.
rewrite (map_hom_add MA MB f t (negA a))  .
rewrite H0.
rewrite map_hom_neg.
apply add_neg.
rewrite H0;reflexivity.
intros.
unfold monomorph.
intros.
apply H.
rewrite map_0.
apply H0.
Qed.

Definition IdentityMorph
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
(Mod:Module eqT addT negT zeroT):
Morph Mod Mod
:=
{|
func := fun a : T => a;
map_0 := reflexivity zeroT;
map_hom_add := fun a1 a2 : T => reflexivity (addT a1 a2);
map_hom_neg := fun a : T => reflexivity (negT a);
well_morph := fun (a1 a2 : T) (H : eqT a1 a2) => H |}.
(*refine (mkMorph
T T eqT eqT addT addT negT negT zeroT zeroT Mod Mod
  (fun a:T=>a:T) _ _ _ _).
reflexivity.
reflexivity.
reflexivity.
auto.
Qed.*)
Print IdentityMorph.

Theorem identity_mono
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
{Mod:Module eqT addT negT zeroT}
:monomorph (IdentityMorph Mod).
unfold monomorph.
unfold IdentityMorph.
unfold func.
auto.
Qed.

Definition epimorph
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f:Morph MA MB)
:Prop:=
forall b:TB,exists a:TA,
eqB(func MA MB f a)b.
Theorem identity_epi
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
{Mod:Module eqT addT negT zeroT}
:epimorph (IdentityMorph Mod).
unfold epimorph.
unfold func;unfold IdentityMorph.
intro b;exists b;reflexivity.
Qed.

Notation "[ f , a ]":=(func _ _ f a).

Definition isin_kernel
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f:Morph MA MB)
(a:TA)
:Prop:=eqB [f ,a ]zeroB.
Print isin_kernel .

Definition kernel
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f:Morph MA MB)
:Set:={a:TA|isin_kernel f a}.


Theorem mono_kernel
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f:Morph MA MB)
:monomorph f<->(forall a:TA,isin_kernel f a<->eqA a zeroA).
split.
intro.
unfold monomorph in H.
intro;split.
apply H.
intro.
unfold isin_kernel.
rewrite H0.
apply map_0.
intro.
unfold monomorph.
apply H.
Qed.
Definition isin_image
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f:Morph MA MB)
(b:TB)
:Prop:=exists a:TA,
eqB[f,a]b.



Definition exact_3
{TA TB TC:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{eqC:TC->TC->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{addC:TC->TC->TC}
{negA:TA->TA}
{negB:TB->TB}
{negC:TC->TC}
{zeroA:TA}
{zeroB:TB}
{zeroC:TC}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
{MC:Module eqC addC negC zeroC}
(f:Morph MA MB)
(g:Morph MB MC)
:Prop:=forall b:TB,
isin_kernel g b<->isin_image f b.
Definition ZeroModule:Module 
(fun _ _:unit=>True)
(fun _ _:unit=>tt)
(fun _:unit=>tt)
tt.
split.
split.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
Qed.


Theorem mono_0AB
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
:forall(f:Morph MA MB),
exact_3 (ZeroMorph ZeroModule MA)
f<->monomorph f.
intros.
split.
unfold exact_3.
intros.
unfold monomorph.
intros.
unfold isin_kernel in H.
unfold isin_image in H.
apply H in H0.
elim H0.
unfold func.
unfold ZeroMorph.
intros.
rewrite <-H1.
reflexivity.
unfold monomorph.
unfold exact_3.
intros.
split.
intro.
exists tt.
unfold func.
unfold ZeroMorph.
symmetry.
apply H.
apply H0.
intro.
elim H0.
intro x.
unfold func.
unfold ZeroMorph.
intro.
unfold isin_kernel.
rewrite <-H1.
apply map_0.
Qed.


Definition cokernel
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f:Morph MA MB)
:Module 
(fun b1 b2:TB=>isin_image f (addB b1 (negB b2)))
addB
negB
zeroB.
split.
split.
unfold Reflexive.
intro.
unfold isin_image.
exists zeroA.
rewrite add_neg.
apply map_0.
unfold Symmetric.
unfold isin_image.
intros.
elim H.
intros.
exists (negA x0).

auto.
rewrite map_hom_neg.
rewrite H0.
Theorem neg_add
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
:forall Mod:Module eqT addT negT zeroT,
forall a b:T,
eqT (negT (addT a b))(addT (negT a)(negT b)).
intros.
apply (ModTheo.rm_common Mod (addT a b)).
rewrite comm_addT.
rewrite add_neg.
rewrite assoc_addT.
rewrite (comm_addT a b) .
rewrite <-(assoc_addT (negT b)).
rewrite (comm_addT (negT b)).
rewrite add_neg.
rewrite comm_addT.
rewrite <-(comm_addT a).
rewrite add_0.
rewrite add_neg.
reflexivity.
Qed. 

rewrite (neg_add MB x (negB y)).
Theorem neg_neg
{T:Set}
{eqT:T->T->Prop}
{addT:T->T->T}
{negT:T->T}
{zeroT:T}
{Mod:Module eqT addT negT zeroT}:
forall a:T,
eqT (negT (negT a))a.
intros.
apply (ModTheo.rm_common Mod (negT a) (negT (negT a)) a).
rewrite comm_addT.
rewrite add_neg.
rewrite add_neg.
reflexivity.
Qed.
rewrite neg_neg.
rewrite comm_addT.
reflexivity.
unfold Transitive.
intros. elim H. elim H0;intros.
exists (addA x1 x0).
rewrite map_hom_add.
rewrite H1;rewrite H2.
rewrite assoc_addT.
rewrite <-(assoc_addT (negB y)).
rewrite (comm_addT (negB y)).
rewrite add_neg.
rewrite (comm_addT zeroB).
rewrite add_0.
reflexivity.
intros.
elim H;elim H0;intros.
exists (addA x0 x).
rewrite map_hom_add.
rewrite H1;rewrite H2.
rewrite (neg_add MB a2 b2).
apply ModTheo.swap_2_in_4.
intros.
elim H;intros.
exists (negA x).
rewrite neg_neg.
rewrite map_hom_neg.
rewrite H0.
rewrite (neg_add MB a1).
rewrite neg_neg.
reflexivity.
intros.
exists zeroA.
rewrite (comm_addT a).
rewrite add_neg.
apply map_0.
intros.
exists zeroA.
rewrite add_0.
rewrite add_neg.
apply map_0.
intros. exists zeroA.
rewrite add_neg;rewrite (ModTheo.neg_zero MB).
rewrite add_0;apply map_0.
intros.
exists zeroA.
rewrite (assoc_addT a b c).
rewrite add_neg.
apply map_0.
Qed.

Print ZeroMorph.

Definition compmorph
{TA TB TC:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{eqC:TC->TC->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{addC:TC->TC->TC}
{negA:TA->TA}
{negB:TB->TB}
{negC:TC->TC}
{zeroA:TA}
{zeroB:TB}
{zeroC:TC}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
{MC:Module eqC addC negC zeroC}
(g:Morph MB MC)
(f:Morph MA MB)
:Morph MA MC
(*apply (mkMorph TA TC _ _ _ _ _ 
_ zeroA zeroC MA MC(fun a:TA=>[g,[f,a]])).

intros.
rewrite map_0.
apply map_0.
intros.
rewrite map_hom_add.
rewrite map_hom_add.
reflexivity.
intros.
rewrite map_hom_neg;rewrite map_hom_neg;reflexivity.
intros.
rewrite H;reflexivity.
Qed.
Print compmorph.*)
:={|
func := fun a : TA => [g, [f, a]];
map_0 := Morphisms.trans_co_eq_inv_impl_morphism PER_Transitive
           [g, [f, zeroA]] [g, zeroB]
           (ModTheo.well_morph_x_Proper g [f, zeroA] zeroB (map_0 MA MB f))
           zeroC zeroC (Morphisms.eq_proper_proxy TC zeroC) (map_0 MB MC g);
map_hom_add := fun a1 a2 : TA =>
               Morphisms.trans_co_eq_inv_impl_morphism PER_Transitive
                 [g, [f, addA a1 a2]] [g, addB [f, a1] [f, a2]]
                 (ModTheo.well_morph_x_Proper g [f, addA a1 a2]
                    (addB [f, a1] [f, a2]) (map_hom_add MA MB f a1 a2))
                 (addC [g, [f, a1]] [g, [f, a2]])
                 (addC [g, [f, a1]] [g, [f, a2]])
                 (Morphisms.eq_proper_proxy TC
                    (addC [g, [f, a1]] [g, [f, a2]]))
                 (Morphisms.trans_co_eq_inv_impl_morphism PER_Transitive
                    [g, addB [f, a1] [f, a2]]
                    (addC [g, [f, a1]] [g, [f, a2]])
                    (map_hom_add MB MC g [f, a1] [f, a2])
                    (addC [g, [f, a1]] [g, [f, a2]])
                    (addC [g, [f, a1]] [g, [f, a2]])
                    (Morphisms.eq_proper_proxy TC
                       (addC [g, [f, a1]] [g, [f, a2]]))
                    (reflexivity (addC [g, [f, a1]] [g, [f, a2]])));
map_hom_neg := fun a : TA =>
               Morphisms.trans_co_eq_inv_impl_morphism PER_Transitive
                 [g, [f, negA a]] [g, negB [f, a]]
                 (ModTheo.well_morph_x_Proper g [f, negA a] (negB [f, a])
                    (map_hom_neg MA MB f a)) (negC [g, [f, a]])
                 (negC [g, [f, a]])
                 (Morphisms.eq_proper_proxy TC (negC [g, [f, a]]))
                 (Morphisms.trans_co_eq_inv_impl_morphism PER_Transitive
                    [g, negB [f, a]] (negC [g, [f, a]])
                    (map_hom_neg MB MC g [f, a]) (negC [g, [f, a]])
                    (negC [g, [f, a]])
                    (Morphisms.eq_proper_proxy TC (negC [g, [f, a]]))
                    (reflexivity (negC [g, [f, a]])));
well_morph := fun (a1 a2 : TA) (H : eqA a1 a2) =>
              Morphisms.trans_co_eq_inv_impl_morphism PER_Transitive
                [g, [f, a1]] [g, [f, a2]]
                (ModTheo.well_morph_x_Proper g [f, a1] [f, a2]
                   (ModTheo.well_morph_x_Proper f a1 a2 H)) [g, [f, a2]]
                [g, [f, a2]] (Morphisms.eq_proper_proxy TC [g, [f, a2]])
                (reflexivity [g, [f, a2]]) |}.


Theorem mono_comp
{TA TB TC:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{eqC:TC->TC->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{addC:TC->TC->TC}
{negA:TA->TA}
{negB:TB->TB}
{negC:TC->TC}
{zeroA:TA}
{zeroB:TB}
{zeroC:TC}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
{MC:Module eqC addC negC zeroC}
(f:Morph MA MB)
(g:Morph MB MC)
:
(monomorph (compmorph g f)->monomorph f)
/\(monomorph f/\monomorph g->monomorph(compmorph g f)).
split.
unfold monomorph.
unfold compmorph.
simpl.
intro.
intros.
apply H.
rewrite H0.
apply map_0.
unfold monomorph.
unfold compmorph.
simpl.
intros.

apply H;apply H;apply H0.
Qed.


Definition KernelModule
{TA TB:Set}
{eqA:TA->TA->Prop}
{eqB:TB->TB->Prop}
{addA:TA->TA->TA}
{addB:TB->TB->TB}
{negA:TA->TA}
{negB:TB->TB}
{zeroA:TA}
{zeroB:TB}
{MA:Module eqA addA negA zeroA}
{MB:Module eqB addB negB zeroB}
(f:Morph MA MB):Module (T:=kernel f)
eqA addA negA zeroA.



Definition ker_morph
{TL1 TL2 TM1 TM2:Set}
{eqL1:TL1->TL1->Prop}
{eqL2:TL2->TL2->Prop}
{eqM1:TM1->TM1->Prop}
{eqM2;TM2->TM2->Prop}
{addL1:TL1->TL1->TL1}
{addL2:TL2->TL2->TL2}
{addM1:TM1->TM1->TM1}
{addM2:TM2->TM2->TM2}
{negL1:TL1->TL1}
{negL2:TL2->TL2}
{negM1:TM1->TM1}
{negM2:TM2->TM2}
{zeroL1:TL1}
{zeroL2:TL2}
{zeroM1:TM1}
{zeroM2:TM2}
{ML1:Module eqL1 addL1 negL1 zeroL1}
{ML2:Module eqL2 addL2 negL2 zeroL2}
{MM1:Module eqM1 addM1 negM1 zeroM1}
{MM2:Module eqM2 addM2 negM2 zeroM2}
(f1:Morph ML1 ML2)
(g1:Morph MM1 MM2)
(v1:Morph ML1 MM1)
(v2:Morph ML2 MM2)
:Morph

