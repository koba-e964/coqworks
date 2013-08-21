Add LoadPath ".".

Require Import "MyNat".

Lemma ySx:forall x y:MyNat,
(y<x\/y=x)<->y<S x.
intros.
split.
intros.
elim H.
intro.
elim H0.
intro.
exists (S x0).
simpl.
simpl in H1.
rewrite H1.
auto.
intro.
exists O.
rewrite H0.
auto.

intros.
elim H.
intro.
elim x0.
intro.
right.
simpl in H0.
apply Ax2.
auto.
intros.
left.
exists m.
simpl. simpl in H1.
apply Ax2.
auto.
Qed.





Lemma L3:forall P:MyNat->Prop,
forall x:MyNat,
((forall y:MyNat,y<x->P y)/\P x)
->(forall y:MyNat,y<S x->P y).
intros P x H0 y.
elim (ySx x y) .
intros.
apply H1 in H2.
elim H2.
apply H0.
intro.
rewrite->H3.
apply H0.
Qed.
Lemma L4:forall P:MyNat->Prop,
(forall x:MyNat,(forall y:MyNat,y< x->P y)
->P x)
->forall x y:MyNat,y<x->P y.
intros P H0 x.
elim x.
intros.
apply False_ind.
apply (MagRel1 y O).
elim y.
auto.
intros.
right. exists m. apply Comm.
apply H.
intros m H1.
apply L3.
split.
apply H1.
apply H0.
apply H1.
Qed.
Theorem SAI :
forall P:MyNat->Prop,
(forall x:MyNat,
(forall y:MyNat,y<x->P y)->P x)
->(forall x:MyNat,P x).
intros.
apply L4 with (x:=S x).
apply H.
exists O.
auto.
Qed.




