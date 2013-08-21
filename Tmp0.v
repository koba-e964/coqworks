Definition NNPP:=forall Q:Prop,~~Q->Q.

Theorem T0:
forall A:Set->Prop,
forall P:Prop,
((exists x:Set,A x)->P)->forall x:Set,(A x->P).

intros.
apply H.
exists x.
apply H0.
Qed.

Theorem T1:
forall A:Set->Prop,
forall P:Prop,
(forall x:Set,(A x->P))->((exists x:Set,A x)->P).
intros.
elim H0.
apply H.
Qed.

Theorem T2:
forall A:
Set->Prop,
forall P:Prop,
NNPP->((forall x:Set,A x)->P)
->(exists x:Set,(A x->P)).
intros.
assert(~forall x:Set,(A x/\~P)).
intro.
apply H1.
Variable x:Set.
apply x.
apply H0.
apply H1.
apply H.
intro.
elim H1.
intros.
split.
apply H.
intro.
elim H2.
exists x0.
intro.
elim H3.
apply H4.
intro.
apply H2.
exists x.
intros.
apply H3.
Qed.

Theorem T2_1:forall A:
Set->Prop,
forall P:Prop,
NNPP->((forall x:Set,A x)->P)
->(exists x:Set,(A x->P)).

intros.
apply H.
intro.
assert (forall x:Set,(A x/\~P)).
intros.
split.
apply H.
intro.
apply H1.
exists x0.
intro.
elim H2.
apply H3.
intro.
elim H1.
exists x0.
intro.
apply H2.

assert P.
apply H0.
intro.
apply H2.
apply H2.
apply x.
apply H3.
Qed.

Theorem curry:
forall P:nat->nat->Prop,
(forall a:nat,{b:nat|P a b})
->{f:nat->nat|forall i:nat,P i (f i)}.

intros.
refine (fun i:nat=> match (H i)as Hk return
{f : nat -> nat | forall i : nat, P i (f i)}
with
|exist ci Hi=>_
end) .


exists (fun i:nat=>
match (H i) with 
|exist ci Hi=>ci end).
intro.





