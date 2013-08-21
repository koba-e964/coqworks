Definition NNPP : Prop:=forall P:Prop,~~P->P.


Theorem T37:
forall P:Set->Prop,
forall A:Prop,
(exists x:Set,(P x->A))
->(forall x:Set,P x)->A.
intros.
elim H.
intros.
apply H1.
apply H0.
Qed.

Lemma T38_1:
forall P:Set->Prop,
forall A:Prop,
NNPP->
~(exists x:Set,(P x ->A))
->(forall x:Set,P x).
intros.
apply H.
intro.
elim H0.
exists x.
intros.
elim H1.
apply H2.
Qed.

Theorem T38:
forall P:Set->Prop,
forall A:Prop,
NNPP->
((forall x:Set,P x)->A)
->
(exists x:Set,(P x->A)).
intros.
apply H.
intro.
elim H1.
Variable x:Set.
exists x.
intro.
apply H0.
eapply T38_1.
apply H.
apply H1.
Qed.

Theorem T35:
forall P:Set->Prop,
forall A:Prop,
(exists x:Set,(A->P x))
->A->(exists x:Set,P x).
intros.
elim H.
intros.
exists x0.
apply H1.
apply H0.
Qed.

Theorem T36:
forall P:Set->Prop,
forall A:Prop,
NNPP->
(A->(exists x:Set,P x))
->exists x:Set,(A->P x).
intros.
apply H.
intro.
elim H1.
exists x.
intros.
apply False_ind.
elim H0.
intros.
elim H1.
exists x0.
intro.
apply H3.
apply H2.
Qed.

