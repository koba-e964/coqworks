Definition NNPP : Prop:=forall P:Prop,~~P->P.


Theorem T4142:
forall P:Set->Prop,
forall Q:Set->Prop,
(forall x:Set,P x/\Q x)
<->((forall x:Set,P x)/\(forall x:Set,Q x)).
Proof.
intros.
split.
intros.
split.
apply H.
apply H.
intros.
split.
elim H.
intros.
apply H0.
elim H.
intros.
apply H1.
Qed.



Theorem T43:
forall P:Set->Prop,
forall Q:Set->Prop,
((forall x:Set,P x)\/(forall x:Set,Q x))->(forall x:Set,P x\/Q x).
intros.
elim H.
left.
apply H0.
right.
apply H0.
Qed.

Variable y:Set.
Variable x:Set.
Axiom (Temp001:~(y=x)).
Theorem T44:
NNPP->
~(
forall P:Set->Prop,
forall Q:Set->Prop,
(forall x:Set,P x \/Q x)->
((forall x:Set,P x)\/(forall x:Set,Q x))).
intro.
Definition P0(x0:Set):Prop:=x=x0.
Definition Q0(x0:Set):Prop:=~(x=x0).
assert (exists P:Set->Prop,exists Q:Set->Prop,(forall x:Set,P x\/Q x)/\(exists x:Set,~P x)/\(exists x:Set,~Q x)).
exists P0.
exists Q0.
split.
compute.
intros.
apply H.
intro.
elim H0.
right.
intro.
apply H0.
left.
apply H1.
split.
exists y.
compute.
intro.
apply (Temp001).
symmetry.
apply H0.
exists x.
compute.
intros.
apply H0.
reflexivity.
intro.
elim H0.
intros.
elim H2.
intros.
elim H3.
intros.
elim H5.
intros.
elim H6.
apply (H1 x0 x1). 
apply (H1 P0 Q0).
apply H0.
apply  (H P0 Q0).
