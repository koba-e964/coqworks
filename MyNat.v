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

Fixpoint mul(a b:MyNat):MyNat:=
match b with
|O =>O
|S b' => (mul a b')+a
end.
Infix "*":=mul.

Definition multOf(x y:MyNat):Prop:=
exists z:MyNat,z*x=y.
Infix "||":=multOf.

Definition isPrime(x:MyNat):Prop:=
S O<x /\forall y:MyNat,(y||x)->y=S O \/ y=x.

Lemma mult_comm:
forall x y:MyNat,
x*y=y*x.
intros.
elim x.
simpl.
elim y.
auto.
intros.
simpl.
auto.
intros.
simpl.
rewrite <-H.
elim y.
simpl. auto.
intros.
simpl.
rewrite H0.
rewrite <-(Assoc (m*m0) m0 m).
rewrite <-(Assoc (m*m0) m m0).
rewrite (Comm m0 m).
auto.
Qed.



Lemma multLtSx:
forall x y:MyNat,
(exists m:MyNat,x=S m)->x||y->y=O\/x<y \/x=y.
intros.
elim H.
intro.
intros.
elim H0.
intros x1.
elim x1.
left.
rewrite <-H2.
apply mult_comm.
intros m H2.
elim m.
right. right.
rewrite <- H3.
rewrite mult_comm.
simpl.
rewrite <-Comm.
auto.
intros.
right. left.
Lemma PPMP:forall p q:MyNat,
(exists s:MyNat,p=S s)->(exists s:MyNat,q=S s)
->(exists s:MyNat,p*q=S s).
intros.
elim H.
elim H0.
intros x H1 y H2.
exists (x*y+x+y).
rewrite H1.
rewrite H2.
simpl.
rewrite (mult_comm (S y) x).
simpl.
auto.
Qed.
rewrite <-H4.
elim (PPMP (S m0) x).
intros.
exists x2.
rewrite <-H5.
rewrite mult_comm.
rewrite (mult_comm (S(S m0)) x).
simpl.
rewrite Assoc.
rewrite (Comm x (x*m0)).
auto.
exists  m0.
auto.
exists x0.
auto.
Qed.


Goal isPrime(S (S O)).
split.
exists O.
simpl.
auto.
intro.
elim y.

intros.
apply False_ind.
elim H.
simpl.
intros.
apply (Ax1 (S O)).
rewrite <-H0.
auto.
intro m.
elim m.
intros.
auto.
intro m0.
elim m0.
intros.
auto.
intros.
apply False_ind.
apply multLtSx in H2.
elim H2.
intro.
apply (Ax1 (S O)).
auto.
intro.
elim H3.
intro.
elim H4.
intros.
apply (Ax1 (S(m1+x))).
apply Ax2.
apply Ax2.
simpl H5.

rewrite <-H5.
simpl.
rewrite (Comm (S(S(S m1))) x).
simpl.
rewrite Comm.
auto.
intro.
apply (Ax1 m1).
apply (Ax2).
apply Ax2.
auto.
exists (S(S m1)).
auto.
Qed.

Fixpoint minus(a:MyNat)(b:MyNat):MyNat:=
match b with
|O=>a
|S b'=>
(fix m0 (a:MyNat)( b':MyNat):MyNat:=
match a with
|O=>O
|S a'=>minus a' b'
end)a b'
end.

Infix "-":=minus.


Fixpoint eq(a b:MyNat):bool:=
match b with
|O=>match a with |O=>true|S a'=>false end
|S b'=>match a with|O=>false|S a'=>eq a' b' end
end.
Infix "==":= eq (at level 90).

Theorem eqm:forall m:MyNat,
(m==m)=true.
intros.
elim m.
simpl.
auto.
intros.
simpl.
apply H.
Qed.



Axiom (modpp:MyNat->MyNat->MyNat).
Axiom (modpp_cal:(forall a n:MyNat,(n=O->modpp a n=S a)
/\(n=S a->modpp a n=O)
/\((exists n':MyNat,n=S n')->~n=S a->modpp a n=S a))).

Fixpoint mod(a n:MyNat):MyNat:=
match a with
|O=>O
|S a'=>modpp (mod a' n) n
end.

Theorem moddec:forall a n:MyNat,
n=O \/(mod a n)<n.
Proof.
intros.
elim n.
auto.
intros.
right.
elim a.
simpl.
exists m.
apply Comm.
intros.
simpl.
elim H0.
intros x.
elim x.
simpl.
intros.
apply Ax2 in H1.
rewrite H1.
assert (modpp m (S m)=O).
apply (modpp_cal m (S m)).
auto.
rewrite H2.
exists m.
apply Comm.
intros.
simpl in  H1.
simpl in H2.
apply Ax2 in H2.
assert((modpp (mod m0 (S m))(S m))=(S(mod m0 (S m)))).
apply modpp_cal.
exists m. auto.
intro.
apply Ax2 in H3.
rewrite <-H3 in H2.
assert (S m1=O).
rewrite (Subt0 (S m1) O m).
auto.
rewrite Comm.
rewrite (Comm O m) .
simpl.
apply H2.
apply (Ax1 m1).
apply H4.
rewrite H3.
exists m1.
simpl.
rewrite Comm.
simpl.
rewrite Comm.
rewrite H2.
auto.
Qed.


Axiom (gcd:MyNat->MyNat->MyNat).
Axiom(gcd_cal:forall a b:MyNat,(b=O->gcd a b=a)/\
((exists b':MyNat,b=S b')->gcd a b=gcd b (mod a b))).

Theorem gcd1:forall a b c:MyNat,
c||a /\c||b <-> c|| gcd a b.
intros.
split.




Theorem primedef:
forall x:MyNat,
isPrime x<->(forall a b:MyNat,x||(a*b)->
x||a \/ x||b).
intros.
split.
intros.
elim H.
intros.
elim H0.



