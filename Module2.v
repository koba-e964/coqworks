Require Import Setoid Relations Morphisms.


Class Module:=
mkModule
{
T:Set
;inclT:T->Prop
;eqT:T->T->Prop
;addT:T->T->T
;negT:T->T
;zeroT:T
;equiv_eqT:Equivalence eqT
;well_addT:forall a1 a2 b1 b2:T,eqT a1 a2->eqT b1 b2->eqT(addT a1 b1)(addT a2 b2)
;well_negT:forall a1 a2:T,eqT a1 a2->eqT(negT a1)(negT a2)
;well_inclT:forall a1 a2:T,eqT a1 a2->inclT a1->inclT a2
;closed_addT:
forall a b:T,inclT a->inclT b->inclT(addT a b)
;closed_negT:
forall a:T,inclT a->inclT(negT a)
;assoc_addT:
forall a b c:T,eqT(addT(addT a b)c)(addT a(addT b c))
;addT_a_zero:
forall a:T,eqT(addT a zeroT)a
;addT_zero_a:
forall a:T,eqT(addT zeroT a)a
;addT_a_negT:
forall a:T,eqT(addT a (negT a))zeroT
;addT_negT_a:
forall a:T,eqT(addT (negT a) a)zeroT
;eqT_decisive:
forall a b:T,{eqT a b}+{~eqT a b}
;comm_addT:
forall a b:T,eqT (addT a b)(addT b a)
;non_empty:
exists a:T,inclT a
}.
Add Parametric Relation(M:Module):(@T M) (@eqT M) 
 reflexivity proved by (@Equivalence_Reflexive _ _ equiv_eqT)
 symmetry proved by (@Equivalence_Symmetric _ _ equiv_eqT)
 transitivity proved by (@Equivalence_Transitive _ _ equiv_eqT)
as ModEquiv.

Class Morph
(MA MB:Module)
:=
mkMorph
{
TA:=(@T MA)
;TB:=(@T MB)
;func:(@T MA)->(@T MB)
;hom_add:forall a1 a2:(@T MA),
(eqT:(@T MB)->(@T MB)->Prop)(addT (func a1)(func a2))(func(addT a1 a2))
;hom_neg:forall a:(@T MA),
eqT(negT (func a))(func(negT a))
;well_func:
forall a1 a2:(@T MA),
eqT a1 a2->eqT (func a1)(func a2)
;closed_func:
forall a:(@T MA),
inclT a->inclT (func a)
}.
Add Parametric Morphism
(M:Module):
addT with signature (eqT==>eqT==>eqT) as well_addT_x.
intros x y H x0 y0.
apply well_addT.
auto.
Qed.
Add Parametric Morphism
(M:Module):
negT with signature (eqT==>eqT) as well_negT_x.
apply well_negT.
Qed.
Add Parametric Morphism
(M:Module):
inclT with signature(eqT==>iff) as well_inclT_x.
intros.
split.
apply well_inclT;auto.
apply well_inclT;symmetry;auto.
Qed.
Add Parametric Morphism
{MA MB:Module}
(f:Morph MA MB):
func  with signature (eqT==>eqT) as well_func_x.
apply well_func.
Qed.

Theorem map_0_to_0
{MA MB:Module}
(f:Morph MA MB):
eqT(func zeroT)zeroT.
destruct f.
rewrite <-(addT_a_negT (zeroT)).
rewrite <-hom_add.
rewrite <-hom_neg.
apply addT_a_negT.
Qed.
Theorem rm_common
(M:Module)
:forall a b c,
eqT(addT b a)(addT c a)->eqT b c.
intros.
rewrite <-addT_a_zero.
rewrite <-(addT_a_zero c).
rewrite <-(addT_a_negT a).
rewrite <-assoc_addT.
rewrite <-assoc_addT.
rewrite H.
reflexivity.
Qed.

Theorem neg_add_add
(M:Module):
forall a b:T,
eqT(negT (addT a b))(addT(negT b)(negT a)).
intros.
apply (rm_common M (addT a b)).
rewrite assoc_addT.
rewrite <-(assoc_addT (negT a)).
rewrite addT_negT_a.
rewrite addT_negT_a.
rewrite addT_zero_a.
rewrite addT_negT_a.
reflexivity.
Qed.
Theorem neg_neg
(M:Module):
forall a:T,
eqT(negT(negT a))a.
intros.
apply (rm_common M (negT a)).
rewrite addT_negT_a.
rewrite addT_a_negT.
reflexivity.
Qed.

Theorem neg_zero
(M:Module):
eqT(negT zeroT)zeroT.
rewrite <-addT_a_zero.
apply addT_negT_a.
Qed.
Theorem incl_zero(M:Module):
inclT zeroT.
generalize non_empty.
intro.
destruct H.
rewrite <-(addT_a_negT x).
apply closed_addT.
apply H.
apply closed_negT.
apply H.
Qed.


Definition NegativeMorph
(M:Module):Morph M M:=
{|
func := fun t : T => negT t;
hom_add := fun a1 a2 : T =>
           trans_sym_co_inv_impl_morphism (Equivalence_PER (ModEquiv M))
             (negT (addT a1 a2)) (addT (negT a2) (negT a1))
             (neg_add_add M a1 a2)
             (trans_co_eq_inv_impl_morphism (ModEquiv_Transitive M)
                (addT (negT a1) (negT a2)) (addT (negT a2) (negT a1))
                (comm_addT (negT a1) (negT a2)) (addT (negT a2) (negT a1))
                (addT (negT a2) (negT a1))
                (eq_proper_proxy T (addT (negT a2) (negT a1)))
                (reflexivity (addT (negT a2) (negT a1))));
hom_neg := fun a : T => reflexivity (negT (negT a));
well_func := well_negT ;
closed_func:=closed_negT
|}.

Definition ZeroMorph
(MA MB:Module)
:Morph MA MB:=
{|
func := fun _ : T => zeroT;
hom_add := fun _ _ : T => addT_a_zero zeroT;
hom_neg := fun _ : T => neg_zero MB;
well_func := fun (a1 a2 : T) (_ : eqT a1 a2) => reflexivity zeroT ;
closed_func:=fun (a:T)(_:inclT a)=>(incl_zero MB)|}
.
Print ZeroMorph.

Notation "[ f , a ]":=(@func _ _ f a) .

Goal 
forall MA MB:Module,
forall a:(@T MA),
eqT (@func MA MB (ZeroMorph MA MB) a) (zeroT).
intros.
simpl.
reflexivity.
Qed.

Definition IdentityMorph
(M:Module):Morph M M:=
{|
func := fun t : T => t;
hom_add := fun a1 a2 : T => reflexivity (addT a1 a2);
hom_neg := fun a : T => reflexivity (negT a);
well_func := fun (a1 a2 : T) (H : eqT a1 a2) => H ;
closed_func:=fun(a:T)(H:inclT a)=>H|}
.


Definition CompMorph
{MA MB MC:Module}
(g:Morph MB MC)(f:Morph MA MB):Morph MA MC
:={|
func := fun a : T => [g, [f, a]];
hom_add := fun a1 a2 : T =>
           trans_co_eq_inv_impl_morphism (ModEquiv_Transitive MC)
             (addT [g, [f, a1]] [g, [f, a2]]) [g, addT [f, a1] [f, a2]]
             (hom_add [f, a1] [f, a2]) [g, [f, addT a1 a2]]
             [g, [f, addT a1 a2]] (eq_proper_proxy T [g, [f, addT a1 a2]])
             (trans_co_eq_inv_impl_morphism (ModEquiv_Transitive MC)
                [g, addT [f, a1] [f, a2]] [g, [f, addT a1 a2]]
                (well_func_x_Proper g (addT [f, a1] [f, a2]) [f, addT a1 a2]
                   (hom_add a1 a2)) [g, [f, addT a1 a2]] [g, [f, addT a1 a2]]
                (eq_proper_proxy T [g, [f, addT a1 a2]])
                (reflexivity [g, [f, addT a1 a2]]));
hom_neg := fun a : T =>
           trans_co_eq_inv_impl_morphism (ModEquiv_Transitive MC)
             (negT [g, [f, a]]) [g, negT [f, a]] (hom_neg [f, a])
             [g, [f, negT a]] [g, [f, negT a]]
             (eq_proper_proxy T [g, [f, negT a]])
             (trans_co_eq_inv_impl_morphism (ModEquiv_Transitive MC)
                [g, negT [f, a]] [g, [f, negT a]]
                (well_func_x_Proper g (negT [f, a]) [f, negT a] (hom_neg a))
                [g, [f, negT a]] [g, [f, negT a]]
                (eq_proper_proxy T [g, [f, negT a]])
                (reflexivity [g, [f, negT a]]));
well_func := fun (a1 a2 : T) (H : eqT a1 a2) =>
             well_func [f, a1] [f, a2] (well_func a1 a2 H) ;
closed_func:=fun (a:(@T MA))(H:inclT a)=>(closed_func [f,a] (closed_func a H))
|}
.


Definition isin_kernel
{MA MB:Module}
(f:Morph MA MB)(a:(@T MA)):Prop
:=inclT a/\eqT [f,a] (zeroT:(@T MB)).

Lemma Tmp0:exists a,a=0.
exists 0.
reflexivity.
Qed.
Print Tmp0.
Lemma Tmp1:
exists a:unit,(fun _:unit=>True)a.
exists tt.
auto.
Qed.
Print Tmp1.



Definition ZeroModule:Module:=
{|
T := unit;
inclT := fun _ : unit => True;
eqT := fun _ _ : unit => True;
addT := fun _ _ : unit => tt;
negT := fun _ : unit => tt;
zeroT := tt;
equiv_eqT := {|
             Equivalence_Reflexive := fun _ : unit => I;
             Equivalence_Symmetric := fun (_ _ : unit) (H : True) => H;
             Equivalence_Transitive := fun (_ _ _ : unit) (_ H0 : True) => H0 |};
well_addT := fun (_ _ _ _ : unit) (_ H0 : True) => H0;
well_negT := fun (_ _ : unit) (H : True) => H;
well_inclT := fun (_ _ : unit) (_ H0 : True) => H0;
closed_addT := fun (_ _ : unit) (_ H0 : True) => H0;
closed_negT := fun (_ : unit) (H : True) => H;
assoc_addT := fun _ _ _ : unit => I;
addT_a_zero := fun _ : unit => I;
addT_zero_a := fun _ : unit => I;
addT_a_negT := fun _ : unit => I;
addT_negT_a := fun _ : unit => I;
eqT_decisive := fun _ _ : unit => left (~ True) I;
comm_addT := fun _ _ : unit => I ;
non_empty := ex_intro (fun _:unit=>True) tt I
|}
.

Program Definition KernelModule
{MA MB:Module}
(f:Morph MA MB):Module:=
{|
T := T;
inclT := isin_kernel f;
eqT := eqT;
addT := addT;
negT := negT;
zeroT := zeroT;
equiv_eqT := equiv_eqT;
well_addT := well_addT;
well_negT := well_negT;
well_inclT := _;
closed_addT := _;
closed_negT := _;
assoc_addT := assoc_addT;
addT_a_zero := addT_a_zero;
addT_zero_a := addT_zero_a;
addT_a_negT := addT_a_negT;
addT_negT_a := addT_negT_a;
eqT_decisive := eqT_decisive;
comm_addT := comm_addT ;
non_empty:=_
|}
.
Obligation 1.
unfold isin_kernel in *.
split.
apply (well_inclT a1).
exact H. apply H0.
rewrite <-H.
apply H0.
Qed.
Obligation 2.
unfold isin_kernel in *.
split.
apply (closed_addT a b).
apply H.
apply H0.
rewrite <-hom_add.
destruct H.
rewrite (H1).
destruct H0.
rewrite H2.  
apply addT_a_zero.
Qed.
Obligation 3.
unfold isin_kernel in *.
destruct H.
split.
apply closed_negT.
apply H.
rewrite <-hom_neg.
rewrite H0.
apply neg_zero.
Qed.
Obligation 4.
unfold  isin_kernel.
exists zeroT.
split.
apply incl_zero.
apply map_0_to_0.
Qed.
Definition EqualMorph
{MA MB:Module}
(f g:Morph MA MB):Prop:=
forall a:(@T MA),eqT [f,a][g,a].


Definition isin_image
{MA MB:Module}
(f:Morph MA MB)
(b:(@T MB)):Prop:=inclT b/\
exists a:(@T MA),inclT a/\eqT[f,a]b.
Program Definition ImageModule
{MA MB:Module}
(f:Morph MA MB):Module:=
{|
T := T;
inclT := isin_image f;
eqT := eqT;
addT := addT;
negT := negT;
zeroT := zeroT;
equiv_eqT := equiv_eqT;
well_addT := well_addT;
well_negT := well_negT;
well_inclT :=_;
closed_addT := _;
closed_negT := _
               ;
assoc_addT := assoc_addT;
addT_a_zero := addT_a_zero;
addT_zero_a := addT_zero_a;
addT_a_negT := addT_a_negT;
addT_negT_a := addT_negT_a;
eqT_decisive := eqT_decisive;
comm_addT := comm_addT;
non_empty := _|}.


Add Parametric Relation(MA MB:Module):(Morph MA MB) EqualMorph 
 reflexivity proved by _
 symmetry proved by _
 transitivity proved by _
as MorphEqual.
unfold Reflexive.
unfold EqualMorph.
reflexivity.
unfold Symmetric.
unfold EqualMorph.
intros.
symmetry;apply H.
unfold Transitive.
unfold EqualMorph.
intros.
rewrite <-H0.
apply H.
Qed.
Check MorphEqual.
unfold Transitive.
unfold EqualMorph.
intros.
rewrite H.
apply H0.
Qed.
unfold Symmetric.
unfold EqualMorph.
intros.
symmetry;apply H.
Qed.

unfold Reflexive.
unfold EqualMorph.
reflexivity.
Qed.

Add Parametric Morphism{MA MB:Module}
:(fun k:Morph MA MB=>(@func _ _ k)) with signature (EqualMorph==>eqT==>eqT) as EqMorph_SameVal.
unfold EqualMorph.
intros.
rewrite H0.
apply H.
Qed.
Theorem CompDef{MA MB MC:Module}
:forall f:Morph MA MB,
forall g:Morph MB MC,
forall a:(@T MA),
eqT [CompMorph g f,a][g,[f,a]].
unfold CompMorph.
reflexivity.
Qed.



Program Definition KernelMorph
{L1 L2 M1 M2:Module}
(f1:Morph L1 L2)
(g1:Morph M1 M2)
(v1:Morph L1 M1)
(v2:Morph L2 M2)
(H:EqualMorph (CompMorph v2 f1)(CompMorph g1 v1))
:Morph (KernelModule f1)(KernelModule g1)
:=mkMorph (KernelModule f1)(KernelModule g1) (@func L1 M1 v1) _ _ _ _.
Obligation 1 of KernelMorph  .

intros. 
rewrite <-(@hom_add L1 M1 v1 a1 a2).
reflexivity.
Qed.
Obligation 2 of KernelMorph.
intros.
apply (@hom_neg L1 M1 v1 a).
Qed.
Obligation 3 of KernelMorph.
apply (@well_func L1 M1).
exact H0.
Qed.
Obligation 4 of KernelMorph.
unfold isin_kernel.
intros.
rewrite <-CompDef.
rewrite <-H.
unfold CompMorph;simpl.
split.
apply closed_func.
apply H0.
unfold isin_kernel in H0.

destruct H0.
rewrite H1.
apply map_0_to_0.
Qed.

Print KernelMorph.
Definition MonoMorph
{MA MB:Module}
(f:Morph MA MB):Prop
:=forall a:@T MA,inclT a->eqT [f,a]zeroT->eqT a zeroT.


Theorem KernelMorphMono
{L1 L2 M1 M2:Module}
(f1:Morph L1 L2)
(g1:Morph M1 M2)
(v1:Morph L1 M1)
(v2:Morph L2 M2)
{H:EqualMorph (CompMorph v2 f1)(CompMorph g1 v1)}:
MonoMorph v1->MonoMorph (KernelMorph f1 g1 v1 v2 H).
unfold MonoMorph.
intros.
apply H0.
simpl in H1.
apply H1.
apply H2.
Qed.

Definition exact_3
{MA MB MC:Module}
(f:Morph MA MB)(g:Morph MB MC):Prop:=
forall t:T,
isin_kernel g t<->isin_image f t.

Definition EpiMorph
{MA MB:Module}
(f:Morph MA MB):Prop:=
forall x:(@T MB),inclT x->(exists y:(@T MA),
inclT y/\eqT [f,y]x).

Theorem AB0_Epi{MA MB:Module}:forall f:Morph MA MB,
exact_3 f (ZeroMorph MB ZeroModule)<->EpiMorph f.
intros.
unfold ZeroMorph;
unfold ZeroModule;
unfold exact_3;
simpl.
unfold EpiMorph.
unfold isin_kernel.
simpl.
split.
intros.
destruct (H x).
destruct H1.
split.
apply H0. exact I.
destruct H3.
exists x0.
exact H3.
unfold isin_image.
intros.
split.
intro.
split.
apply H0.
destruct (H t).
apply H0.
exists x.
exact H1.
intro.
split.
apply H0.
auto.
Qed.


Theorem ZeroAB_Mono{MA MB:Module}:forall f:Morph MA MB,
exact_3 (ZeroMorph ZeroModule MA)f<->MonoMorph f.
unfold ZeroMorph;
unfold ZeroModule;
unfold exact_3;
unfold MonoMorph;
simpl.
unfold isin_kernel;
unfold isin_image;
simpl.
intros.
split.
intros.
symmetry.
destruct (H a).
destruct H2.
split. apply H0. apply H1.
destruct H4.
apply H4.
intros.
split.
intros.
split.
apply H0.
split.
apply tt.
split.
auto.
symmetry.
apply (H t).
apply H0.
apply H0.
intros.
split.
apply H0.
SearchAbout and.
destruct (proj2 H0). 
rewrite <-(proj2 H1).
apply map_0_to_0.
Qed.
Obligation 1.
unfold isin_image in *.
split.
rewrite <-H.
apply H0.
destruct (proj2 H0).
exists x.
rewrite <-H.
exact H1.
Qed.
Obligation 2.
unfold isin_image in *.
split.
apply (closed_addT a b).
apply H. apply H0.
destruct (proj2 H).
destruct(proj2 H0).
exists (addT x x0).
split.
apply (closed_addT x x0 (proj1 H1)(proj1 H2)).
rewrite <-hom_add.
rewrite (proj2 H1).
rewrite (proj2 H2).
reflexivity.
Qed.
Obligation 3.
unfold isin_image in *.
split.
apply (closed_negT a (proj1 H)).
destruct (proj2 H).
exists (negT x).
split.
apply (closed_negT x (proj1 H0)).
rewrite <-hom_neg.
rewrite (proj2 H0).
reflexivity.
Qed.
Obligation 4.
exists zeroT.
unfold isin_image.
split.
exact (incl_zero MB).
exists zeroT.
split.
apply incl_zero.
apply map_0_to_0.
Qed.




Program Definition 
Embed{MA MB:Module}
(f:Morph MA MB):Morph (KernelModule f)MA
:=mkMorph (KernelModule f) MA(fun a=>a) _ _ _ _.
Obligation 1 .
reflexivity.
Defined.
Obligation 2 . reflexivity.
Defined.
Obligation 4. unfold isin_kernel in H.
apply H.
Qed.
Obligations.


Require Import ZArith.
Check Zmod.
Print Zmod.
Print Zdiv_eucl_POS.




Program Definition DirectSum
(MA MB:Module)
:Module
:=
{|
T:=(@T MA)*(@T MB)
;inclT:=(fun t:T*T=>match t with(t1,t2)=>inclT t1/\inclT t2 end)
;eqT:=(fun t u:T*T=>match t with(t1,t2)=>
match u with(u1,u2)=>(eqT t1 u1)/\(eqT t2 u2) end end)
;addT:=(fun t u:T*T=>match t with(t1,t2)=>
match u with(u1,u2)=>(addT t1 u1,addT t2 u2) end end)
;negT:=(fun t:T*T=>match t with(t1,t2)=>(negT t1,negT t2)end)
;zeroT:=(zeroT,zeroT)
;equiv_eqT:=_
;well_addT:=_
;well_negT:=_
;well_inclT:=_
;closed_addT:=_
;closed_negT:=_
;assoc_addT:=_
;addT_a_zero:=_
;addT_zero_a:=_
;addT_a_negT:=_
;addT_negT_a:=_
;eqT_decisive:=_
;comm_addT:=_
;non_empty:=_
|}.
Obligation 1.
split.
unfold Reflexive.
intros.
destruct x as[x1 x2].
split.
reflexivity.
reflexivity.
unfold Symmetric.
intros.
destruct x as[x1 x2].
destruct y as[y1 y2].
split.
symmetry.
exact(proj1 H).
symmetry.
exact(proj2 H).
unfold Transitive.
intros.
destruct x as[x1 x2].
destruct y as[y1 y2].
destruct z as[z1 z2].
split.
transitivity y1.
exact (proj1 H).
exact (proj1 H0).
transitivity y2.
exact (proj2 H).
exact(proj2 H0).
Qed.
Obligation 2.
split.
rewrite H.
rewrite H0.
reflexivity.
rewrite H2.
rewrite H1.
reflexivity.
Qed.

Obligation 3.
split.
rewrite H.
reflexivity.
rewrite H0.
reflexivity.
Qed.
Obligation 4.
split.
rewrite <-H.
exact H0.
rewrite <-H2.
exact H1.
Qed.
Obligations.
Obligation 5.
split.
exact (closed_addT _ _ H H0).
exact (closed_addT _ _ H2 H1).
Qed.
Obligation 6.
split.
exact (closed_negT _ H).
exact (closed_negT _ H0).
Qed.
Obligation 7.
split.
apply assoc_addT.
apply assoc_addT.
Qed.
Obligation 8.
split.
apply addT_a_zero.
apply addT_a_zero.
Qed.


Obligation 9.
split.
apply addT_zero_a.
apply addT_zero_a.
Qed.
Obligation 10.
split.
apply (addT_a_negT t).
apply (addT_a_negT).
Qed.
Obligation 11.
split.
apply addT_negT_a.
apply addT_negT_a.
Qed.
Obligation 12.
generalize (eqT_decisive t1 t);intro.
generalize (eqT_decisive t2 t0);intro.
elim H.
elim H0.
intros.
left.
apply (conj a0 a).
intros.
right.
intro.
elim b.
exact (proj2 H1).
intros.
right.
intro.
elim b.
exact (proj1 H1).
Qed.
Obligation 13.
split.
apply comm_addT.
apply comm_addT.
Qed.

Obligation 14.
exists (zeroT,zeroT).
split.
apply incl_zero.
exact (incl_zero MB).
Qed.

Definition universal(M MA:Module)(p:Morph M MA):Prop:=
forall N:Module,forall f:Morph N MA,
exists g:Morph N M,
EqualMorph f (CompMorph p g).
Definition isomorphic(M1 M2:Module):Prop:=
exists p:Morph M1 M2,MonoMorph p/\EpiMorph p.
Theorem iso2:
forall M1 M2:Module, 
isomorphic M1 M2 <->
exists f:Morph M1 M2,
exists g:Morph M2 M1,
EqualMorph (CompMorph g f) (IdentityMorph M1).
intros.
unfold isomorphic.
split.

intro.
destruct H.
destruct H.
exists x.
assert (forall m2:(@T M2),inclT m2->(@T M1)).
unfold EpiMorph in *.
intro m2.
intro.
generalize (H0 m2).
intro.
apply H1 in H2.
refine match H2 return (@T M1) with
ex_intro _ _=>_ end.
exact x0.
refine (mkMorph M2 M1 H1 _ _ _ _).
intros.
rewrite well_addT.
rewrite well_addT.
reflexivity.
reflexivity.
reflexivity.
apply neg_zero.
simpl.
rewrite 
auto.




Theorem univ_iso:
forall M1 M2 MA MB:Module,
forall pa1:Morph M1 MA,
forall pb1:Morph M1 MB,
forall pa2:Morph M2 MA,
forall pb2:Morph M2 MB,
universal M1 MA pa1->universal M1 MB pb1->
universal M2 MA pa2->universal M2 MB pb2->
exists h:Morph M1 M2,
MonoMorph h/\EpiMorph h.
unfold universal.

intros.

destruct (H1 M1 pa1).




