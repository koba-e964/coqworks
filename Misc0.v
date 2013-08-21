Definition classic:Prop:=
forall p:Prop,
~~p->p.
Definition xmid:Prop:=
forall p:Prop,
p\/~p.
Definition peirce:Prop:=
forall p q:Prop,
((p->q)->p)->p.

Definition imply_to_or:Prop:=
forall p q:Prop,
(p->q)->(~p\/q).
Definition dm:Prop:=
forall p q:Prop,
~(~p/\~q)->p\/q.

Theorem c_x:classic<->xmid.
unfold classic,xmid.
split.
intros.
apply H.
intro.
apply H0.
left.
apply H.
intro.
apply H0.
right.
intro.
apply H1.
exact H2.
intros.
elim (H p).
auto.
intro.
elim H0.
exact H1.
Qed.

Theorem cp:
classic<->peirce.
unfold classic,peirce.
split.
intros.
apply H.
intro.
apply H1.
apply H0.
intros.
elim H1.
exact H2.
intros.
apply (H _ False).
intros.
elim H0.
exact H1.
Qed.

Theorem ci:classic<->imply_to_or.
unfold classic,imply_to_or.
split.
intros.
apply H.
intro.
apply H1.
left.
intro.
apply H1.
right.
exact (H0 H2).
intros.
elim (H p p).
intro.
elim H0.
exact H1.
auto.
auto.
Qed.

Theorem cd:classic<->dm.

unfold classic,dm.
split.
intros.
apply H.
intro.
info apply H0.
split.
intro.
apply H1.
info left.
exact H2.


intro.
apply H1.
right.
exact H2.

intros.
elim (H p p).
auto.
auto.
intro.
apply H0.
exact (proj1 H1).
Qed.

Axiom (Cat:Type).
Axiom (Object:Type).

Definition Functor(C D:Cat):=Object->Object.


Axiom (incl:Object->Cat->Prop).

Axiom (eff :forall C D:Cat,Functor C D->Object->Object).


Definition universal(C D:Cat)(U:Functor D C)(X:Object)(_:incl X C)
(A:Object)(_:incl A (eff D C U A)):Prop.


