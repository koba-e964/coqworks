Definition NNPP : Prop:=forall P:Prop,~~P->P.

Theorem T11:
forall P:Set->Prop,
(forall x:Set,P x)
->~(exists x:Set,~P x).
intros.
intro.
elim H0.
intros.
elim H1.
apply H.
Qed.

Theorem T12:
NNPP->
forall P:Set->Prop,
~(exists x:Set,~P x)
->(forall x:Set,P x).
intros.
apply H.
intro.
elim H0.
exists x.
apply H1.
Qed.

Theorem T15:
forall P:Set->Prop,
NNPP->
~(forall x:Set,P x)
->(exists x:Set,~P x).
intros.
apply H.
intro.
elim H0.
intro.
apply H.
intro.
elim H1.
exists x.
tauto.
Qed.
