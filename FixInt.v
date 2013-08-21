Require Import Bool.
Require Import Arith.
Require Import JMeq.
Inductive FixInt:nat->Type:=
|zerobit:FixInt 0
|consbit:forall n,bool->FixInt n->FixInt (S n).

Definition cdrbits{n}(f:FixInt (S n)):FixInt n.
generalize (refl_equal(S n)).
pattern (S n) at 1.
refine match f in FixInt x return x=S n->FixInt n
with
|zerobit=>_
|consbit n' b l=>_
end.
discriminate.
intro.
injection H;intro.
rewrite H0 in l.
exact l.
Defined.

Definition carbit{n}(f:FixInt(S n)):bool.
generalize (refl_equal(S n)).
pattern (S n) at 1.
refine match f in FixInt x return x=S n->bool
with
|zerobit=>_
|consbit n' b l=>_
end.
discriminate.
intro.
exact b.
Defined.


Inductive eq_FixInt:forall n,FixInt n->FixInt n->Prop:=
|eqfi_zero:eq_FixInt 0 zerobit zerobit
|eqfi_cons:forall m,forall v w:FixInt m,forall b:bool,
eq_FixInt m v w->eq_FixInt (S m)(consbit m b v)(consbit m b w).


Theorem FixInt_case:forall n,
forall v:FixInt n,
(n=0->JMeq v zerobit)/\
forall m:nat,n=S m->exists b:bool,exists vv:FixInt m,
JMeq v(consbit m b vv).
intros.
split.
destruct v.
reflexivity.
intros.
discriminate H.
intros.
destruct v.
discriminate H.
exists b.
apply eq_add_S in H.
rewrite<-H.
exists v.
reflexivity.
Qed.


Theorem eq_FixInt_then_eq:forall n,
forall v w:FixInt n,
eq_FixInt n v w->v=w.
intro n.
elim n.
intros.
apply JMeq_eq.
generalize (FixInt_case 0);intro.
destruct (H0 v).
clear H2.
rewrite (H1(refl_equal 0)).
destruct(H0 w).
clear H3.
rewrite(H2(refl_equal 0)).
reflexivity.
intros.
generalize(refl_equal(S n0)).
generalize(JMeq_refl v)(JMeq_refl w).

refine match H0 in eq_FixInt x vv ww return JMeq v vv->JMeq w ww->x=S n0-> v=w
with
|eqfi_zero=>_
|eqfi_cons _ _ _ _ _=>_
end.
discriminate.
intros.
apply eq_add_S in H3.
rewrite<-H3 in H.
generalize(H v0 w0 e);intro.
rewrite H4 in H1.
rewrite<-H2 in H1.
exact (JMeq_eq H1).
Qed.


Fixpoint beq_FixInt{n}(a b:FixInt n):bool.
destruct n.
exact true.
generalize (FixInt_case(S n));intro.
generalize (proj2(H a) n(refl_equal(S n)));intro.
generalize (proj2(H b) n(refl_equal(S n)));intro.
generalize (refl_equal(S n)).
generalize (JMeq_refl b).
refine match b as bb in FixInt x  return JMeq b bb->S n=x->bool
with
|zerobit=>_
|consbit _ _ _=>_
end.
discriminate.
intros.
generalize (refl_equal(S n)).
generalize (JMeq_refl a).
refine match a as aa in FixInt x  return JMeq a aa->S n=x->bool
with
|zerobit=>_
|consbit _ _ _=>_
end.
discriminate.
intros.
apply eq_add_S in H3.
apply eq_add_S in H5.
clear H.
clear H4.
rewrite <-H5 in f0.
clear H2.
rewrite <-H3 in f.
exact (andb (eqb b0 b1)(beq_FixInt n f f0)).
Defined.

Theorem beq_FixInt_eq:
forall n:nat,
forall a b:FixInt n,
beq_FixInt a b=true->a=b.
fix 1.
intro n.
case n.
intros.
generalize ((proj1(FixInt_case 0 a))(refl_equal 0));intro.
generalize ((proj1(FixInt_case 0 b))(refl_equal 0));intro.
rewrite H0.
rewrite H1.
reflexivity.
intros n0 a b.
generalize ((proj2(FixInt_case (S n0) a))n0 (refl_equal (S n0)));intro.
generalize ((proj2(FixInt_case (S n0) b))n0 (refl_equal (S n0)));intro.
destruct H.
destruct H.
destruct H0.
destruct H0.
rewrite H.
rewrite H0.
intros.
simpl in H1.
apply andb_prop in H1.
destruct H1.
apply beq_FixInt_eq in H2.
apply eqb_prop in H1.
rewrite H1.
Guarded.
compute in H2.
change (x2=x0) in H2.
rewrite H2.
apply eqfi_cons.
unfold eq_rec_r in H2.
unfold eq_rec in H2.
unfold eq_rect in H2.
apply H2.





Theorem fix0_is_zerobit:(forall f0:FixInt 0,f0=zerobit).
intro.
generalize (JMeq_refl f0).
generalize (refl_equal 0).
pattern f0 at 1.
pattern 0 at 2.
refine match f0 as ff0 in FixInt x return x=0->JMeq ff0 f0->f0=zerobit
with
|zerobit=>_
|consbit n b l=>_
end.
intros.
rewrite H0.
auto.
discriminate.
Qed.
rewrite (fix0_is_zerobit a).
rewrite (fix0_is_zerobit b).
reflexivity.

intros.
apply JMeq_eq.
generalize (refl_equal (S n0)).
pattern (S n0) at 2.
refine match a as aa in FixInt x  return(S n0=x->JMeq aa b)
with
|zerobit=>_
|consbit n' b l=>_
end.
discriminate.
intro.
apply eq_add_S in H0.
unfold beq_FixInt in H.
generalize (refl_equal (S n0)).
pattern (S n0) at 1.
refine match b as bb in FixInt y  return(y=S n0->JMeq (consbit n' b0 l) bb) 
with
|zerobit=>_
|consbit n' b l=>_
end.
discriminate.
intros.
apply eq_add_S in H1.

destruct H.

SearchAbout JMeq.


case a.
intro b.




