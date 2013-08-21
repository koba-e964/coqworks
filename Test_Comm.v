Inductive MyNat : Set :=
  | O : MyNat
  | S : MyNat -> MyNat.

Fixpoint Plus (a b :MyNat) : MyNat :=
 match b with
 |O => a
 |S b' => S(Plus a  b')
 end.

Infix "+" := Plus.
Theorem Comm : forall ( a b : MyNat),a+b = b+a.


intro a.
elim a.
intro b.
elim b.
reflexivity.
simpl.
intros.
rewrite -> H.
reflexivity.
intro m.
simpl.
intros.
elim b.
rewrite <- H with (b := O).
reflexivity.
intros.
simpl.
rewrite <- H with (b:=S m0).
simpl.
rewrite -> H0.
rewrite -> H .
reflexivity.
Qed.

Theorem Assoc:forall a b c:MyNat,a+(b+c)=(a+b)+c.

	intros.
	elim c.
	simpl.
	auto.
	intros.
	simpl.
	rewrite->H.
	auto.
Qed.
Definition NNPP:Prop:=forall Q:Prop,~~Q->Q.

Theorem E2F:forall P:MyNat->Prop,
~(exists x:MyNat,P x)
->forall x:MyNat,~ P x.
intros.
intro.
elim H.
exists x.
auto.
Qed.

Theorem E2FN:forall P:MyNat->Prop,
NNPP->
~(exists x:MyNat,~P x)
->forall x:MyNat,P x.
intros.
apply H.
intro.
elim H0.
exists x.
auto.
Qed.

Definition LargerThan(x y:MyNat):Prop:=
exists z:MyNat,x+S z=y.
Infix "<" :=LargerThan.
Definition GreaterThan(x y:MyNat):Prop:=
y< x.
Infix ">":=GreaterThan.

Axiom (Ax1:forall x:MyNat,~S x=O).
Axiom (Ax2:forall x y:MyNat,S x=S y->x=y).

Theorem Subt0:forall a b c:MyNat,
a+c=b+c->a=b.
	intros a b c.
	elim c.
	auto.
	intros.
	apply H.
	simpl in H0.
	apply Ax2.
	apply H0.
Qed.
Theorem Subt1:forall a b c:MyNat,
a+c<b+c -> a<b.
	intros.
	elim H.
	intros.
	exists x.
	apply Subt0 with (c:=c).
	rewrite <-H0.
	rewrite <-Assoc with (b:=S x).
	rewrite <-Assoc with (b:=c).
	rewrite Comm with (a:=c).
	auto.
Qed.

Theorem MagRel0:forall a b:MyNat,
a=b \/a<b\/a>b.
	intros.
	elim a.
	elim b.
	auto.
	intros.
	right.
	left.
	exists m.
	apply Comm.

	intros.
	elim H.
	right. right.
	exists O.
	simpl.
	rewrite H0.
	auto.

	intros.
	elim H0.

	intros.
	elim H1.
	intros x.
	elim x.
	intros.
	left.
	auto.
	intros.
	right. left.
	exists m0.
	simpl.
	rewrite Comm.
	simpl.
	rewrite <-H3.
	simpl.
	rewrite Comm.
	auto.

	intro.
	right. right.
	elim H1.
	intros.
	exists (S x).
	rewrite <-H2.
	auto.
Qed.

Theorem MagRel1:forall a b:MyNat,
~(a<b)<->a=b\/a>b.
split.
intros.
elim (MagRel0 a b).
	auto.
	intro.
	elim H0.
	intro.
	elim H.
	auto.
	auto.

	intro.
	intro.
	elim H.
	elim H0.
	intros.
	assert (S x=O).
	apply Subt0 with (c:=a).
	rewrite Comm.
	rewrite (Comm O a) .
	rewrite H1.
	auto.
	apply (Ax1 x).
	auto.
	elim H0.
	intros.
	elim H2.
	intros.
	assert(S x+S x0=O).
	apply Subt0 with (c:=a).
	rewrite Comm.
	rewrite->(Assoc a (S x)).
	rewrite H1.
	rewrite (Comm O a).
	apply H3.
	apply (Ax1 (S x+x0)).
	apply H4.
Qed.


