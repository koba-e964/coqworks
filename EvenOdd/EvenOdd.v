Require Import Setoid.
Require Import Arith.
Require Import Bool.
Module EvenAndOdd.
Inductive even:nat->Prop:=
|even_0:even 0
|even_SS:forall n,even n->even(S(S n)).

Inductive odd:nat->Prop:=
|odd_1:odd 1
|odd_SS:forall n,odd n->odd(S(S n)).

Theorem even_add_SS:
forall n,
even(S(S n))->even n.
Proof.
intros.
generalize (refl_equal(S(S n))).
pattern(S(S n))at 2.
case H.
discriminate.
intros.
repeat apply eq_add_S in H1.
rewrite H1.
exact H0.
Qed.

Theorem odd_add_SS:forall n,
odd(S(S n))->odd n.
intros.
generalize (refl_equal(S(S n))).
pattern(S(S n))at 2.
info case H.
info discriminate.
intros.
repeat apply eq_add_S in H1.

rewrite H1.
exact H0.
Qed.
Lemma even_S:
forall n,
even n->odd (S n).
intros.
elim H.
exact odd_1.
intros.
apply odd_SS.
exact H1.
Qed.
Lemma odd_S:
forall n,
odd n->even (S n).
intros.
elim H.
exact (even_SS 0 even_0).
intros.
apply even_SS.
exact H1.
Qed.

Lemma even_S_iff:
forall n,
even n<->odd(S n).
intro.
split.
apply even_S.
intros.
apply even_add_SS.
apply odd_S.
exact H.
Qed.

Lemma odd_S_iff:
forall n,
odd n<->even(S n).
intro.
split.
apply odd_S.
intros.
apply odd_add_SS.
apply even_S.
exact H.
Qed.



Lemma even_odd_dec:
forall n,
{even n}+{odd n}.
induction n.
left.
apply even_0.
case IHn.
right.
exact (even_S n e).
left.
exact (odd_S n o).
Qed.


Lemma even_and_odd:
forall n,
even n->odd n->False.
induction n.
intros.
generalize (refl_equal 0).
pattern 0 at 2.
case H0;
discriminate.

intros.
rewrite <-odd_S_iff in H.
rewrite <-even_S_iff in H0.
exact(IHn H0 H).
Qed.


Fixpoint beven(n:nat):bool:=
match n with
|0=>true
|1=>false
|S(S n')=>beven n'
end.

Lemma beven_true:
forall n:nat,
beven n=true->even n.
fix IHn 1.
intro.
case_eq n.
intros.
exact even_0.
intro;case n0.
discriminate.
intros.
apply even_SS.
apply IHn.
simpl in H0.
exact H0.
Qed.
Lemma beven_true_iff:
forall n,
beven n=true<->even n.
intros.
split.
apply beven_true.
intros.
elim H.
auto.
intros.
exact H1.
Qed.
Lemma beven_false:
forall n,
beven n=false->odd n.
intros.
assert(~even n).
rewrite <-beven_true_iff.
rewrite H.
SearchPattern(false<>true).
apply diff_false_true.
case (even_odd_dec n);auto.
intros.
case H0.
exact e.
Qed.

Lemma beven_false_iff:
forall n,
beven n=false<->odd n.
intro.
split.
apply beven_false.
intros.
apply not_true_is_false.
intro.
apply beven_true in H0.
exact (even_and_odd n H0 H).
Qed.



Theorem even_is_mul_2:
forall n,
even n->exists x,n=2*x.
simpl.

intros.
elim H.
exists 0.
auto.
intros.
destruct H1.
exists (S x).
rewrite H1.
simpl.
rewrite (plus_comm x 0).
simpl.
rewrite plus_n_Sm.
info auto.
Qed.
Theorem odd_is_S_mul_2:
forall n,
odd n->exists x,n=S(2*x).
Proof.
intros.
elim H.
exists 0;auto.
intros.
destruct H1.
exists (S x).
rewrite H1.
simpl.
rewrite (plus_comm x 0).
simpl.
rewrite plus_n_Sm.
info auto.
Qed.


Theorem even_plus_odd_is_odd:
forall x y:nat,
even x->odd y->
odd(x+y).
intros.
elim H.
apply H0.
intros.
simpl.
apply odd_SS.
apply H2.
Qed.

End EvenAndOdd.

Section OddIsNotEven.
Inductive even:nat->Prop:=
|even_0:even 0
|even_SS:forall n,even n->even(S(S n)).
Definition odd(n:nat):Prop:=
~even n.
Theorem even_add_SS:
forall n,
even(S(S n))->even n.
Proof.
intros.
generalize (refl_equal(S(S n))).
pattern(S(S n))at 2.
case H.
discriminate.
intros.
repeat apply eq_add_S in H1.
rewrite H1.
exact H0.
Qed.

Theorem odd_add_SS:forall n,
odd(S(S n))->odd n.
intros.
intro.
apply H.
apply even_SS.
exact H0.
Qed.
Theorem odd_SS:
forall n,
odd n->odd(S(S n)).
intros n H H0.
apply H.
apply even_add_SS.
exact H0.
Qed.

Lemma odd_1:odd 1.
intro.
generalize (refl_equal 1).
pattern 1 at 2.
case H;discriminate.
Qed.




Lemma even_S:
forall n,
even n->odd (S n).
intros.
elim H.
exact odd_1.
intros.
apply odd_SS.
exact H1.
Qed.
Lemma odd_S:
forall n,
odd n->even (S n).
fix IHn 1.
induction n.
intros.
elim H.
exact even_0.
case_eq n.
intros.
apply even_SS.
exact even_0.
intros.
apply even_SS.
apply odd_add_SS in H0.
apply IHn.
apply H0.
Qed.

Lemma even_S_iff:
forall n,
even n<->odd(S n).
intro.
split.
apply even_S.
intros.
apply even_add_SS.
apply odd_S.
exact H.
Qed.

Lemma odd_S_iff:
forall n,
odd n<->even(S n).
intro.
split.
apply odd_S.
intros.
apply odd_add_SS.
apply even_S.
exact H.
Qed.



Lemma even_odd_dec:
forall n,
{even n}+{odd n}.
induction n.
left.
apply even_0.
case IHn.
right.
exact (even_S n e).
left.
exact (odd_S n o).
Qed.


Lemma even_and_odd:
forall n,
even n->odd n->False.
auto.
Qed.


Fixpoint beven(n:nat):bool:=
match n with
|0=>true
|1=>false
|S(S n')=>beven n'
end.

Lemma beven_true:
forall n:nat,
beven n=true->even n.
fix IHn 1.
intro.
case_eq n.
intros.
exact even_0.
intro;case n0.
discriminate.
intros.
apply even_SS.
apply IHn.
simpl in H0.
exact H0.
Qed.
Lemma beven_true_iff:
forall n,
beven n=true<->even n.
intros.
split.
apply beven_true.
intros.
elim H.
auto.
intros.
exact H1.
Qed.
Lemma beven_false:
forall n,
beven n=false->odd n.
intros.
unfold odd.
rewrite <-beven_true_iff.
rewrite H.
SearchPattern(false<>true).
apply diff_false_true.
Qed.

Lemma beven_false_iff:
forall n,
beven n=false<->odd n.
intro.
split.
apply beven_false.
intros.
apply not_true_is_false.
intro.
apply beven_true in H0.
exact (even_and_odd n H0 H).
Qed.



Theorem even_is_mul_2:
forall n,
even n->exists x,n=2*x.
simpl.

intros.
elim H.
exists 0.
auto.
intros.
destruct H1.
exists (S x).
rewrite H1.
simpl.
rewrite (plus_comm x 0).
simpl.
rewrite plus_n_Sm.
info auto.
Qed.
Theorem odd_is_S_mul_2:
forall n,
odd n->exists x,n=S(2*x).
Proof.
fix IHn 1.
intro n.
case n.
 intros.
 absurd (even 0).
 exact H.
 exact even_0.

intro n0.
case n0.
 intros.
 exists 0.
 auto.
intros.
apply odd_add_SS in H.
destruct (IHn n1 H).
exists (S x).
simpl in *.
rewrite H0.
rewrite plus_n_Sm.
reflexivity.
Qed.


Theorem even_plus_odd_is_odd:
forall x y:nat,
even x->odd y->
odd(x+y).
intros.
elim H.
apply H0.
intros.
simpl.
apply odd_SS.
apply H2.
Qed.
