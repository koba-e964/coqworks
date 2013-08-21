Require Import Setoid Relations Morphisms.

Record TypeWithEquality:Type :=
{
TWE_Type:Type;
TWE_Equality:relation TWE_Type;
TWE_Equivalence:Equivalence TWE_Equality
}.

Record ArrowWithEquality(A B:TypeWithEquality):Type
:=
{
AWE_Arrow:TWE_Type A->TWE_Type B;
AWE_Compat:Proper (TWE_Equality A==> TWE_Equality B)%signature AWE_Arrow
}.

Implicit Arguments Build_ArrowWithEquality[A B].
Implicit Arguments AWE_Arrow[A B].
Implicit Arguments AWE_Compat[A B].

Program Definition MakeArrowWithEquality(A B:TypeWithEquality):TypeWithEquality
:=Build_TypeWithEquality
	(ArrowWithEquality A B)
	(fun f1 f2=> forall x y,TWE_Equality A x y->TWE_Equality B(AWE_Arrow f1 x)(AWE_Arrow f2 y))
	_.

Next Obligation.
destruct A as(AT,AE,AEV).
destruct B as(BT,BE,BEV).
split;
unfold Reflexive,Symmetric,Transitive.
intros (fA,fC);intros.
simpl in *.
rewrite H.
reflexivity.
intros (fA, fC)(gA,gC);
intros.
simpl in *.
rewrite H0.
symmetry.
apply H.
reflexivity.
intros (fA,fC) (gA,gC) (hA,hC);intros.
simpl in *.
rewrite H1.
transitivity (gA y).
apply H.
reflexivity.
apply H0.
reflexivity.
Qed.


Notation "x -> y" :=(x -> y) (at level 90, right
associativity):type_scope.


Delimit Scope TypeWithEquality_scope with TypeWithEquality.
Infix "->":=MakeArrowWithEquality(at level 90, right associativity):TypeWithEquality_scope.
Module Type IsMonad.
 Parameter m:TypeWithEquality -> TypeWithEquality.
 Parameter returnM:  forall {t:TypeWithEquality},TWE_Type (t->m t)%TypeWithEquality.
 Parameter bindM:forall {t1 t2:TypeWithEquality},TWE_Type(m t1->(t1->m t2)->m t2)%TypeWithEquality.
 Axiom monad_bind_return_r:forall (t1 t2:TypeWithEquality) (a:TWE_Type t1)
  (k:TWE_Type (t1-> m t2)%TypeWithEquality),
  TWE_Equality (m t2)(AWE_Arrow (AWE_Arrow bindM(AWE_Arrow returnM a))k)(AWE_Arrow k a).


Axiom monad_bind_return_l:forall{t:TypeWithEquality}(ma:TWE_Type (m t)),
TWE_Equality(m t) (AWE_Arrow(AWE_Arrow bindM ma)returnM)ma.

Axiom monad_bind_assoc:forall{t1 t2 t3:TypeWithEquality}
(ma:TWE_Type (m t1))(k:TWE_Type(t1->m t2)%TypeWithEquality)(h:TWE_Type(t2->m t3)%TypeWithEquality),
TWE_Equality(m t3)
(AWE_Arrow(AWE_Arrow bindM ma)
(Build_ArrowWithEquality(fun x=>AWE_Arrow(AWE_Arrow bindM (AWE_Arrow k x))h)
(fun(x y:TWE_Type t1)(Hxy:TWE_Equality t1 x y)=>AWE_Compat bindM
(AWE_Arrow k x)(AWE_Arrow k y)(AWE_Compat k x y Hxy)h h
(Equivalence_Reflexive(Equivalence:=TWE_Equivalence _)h
)
)
)
)
(AWE_Arrow(AWE_Arrow bindM(AWE_Arrow(AWE_Arrow bindM ma)k))h).
End IsMonad.
