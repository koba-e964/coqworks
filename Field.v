Require Import QArith.


Class Field(S:Set)
(add:S->S->S)
(neg:S->S)
(mult:S->S->S)
(inv:S->S)
(unity:S)
(zero:S)
(eq:S->S->Prop):={
add_comm:forall a b:S,eq( add a b)(add b a)
;add_assoc:forall a b c:S,
eq(add (add a b)c)(add a(add b c))
;add_zero_a:forall a:S,eq(add zero a)a
;add_neg_a:forall a:S,eq(add (neg a) a ) zero
;mult_comm:forall a b:S,eq(mult a b)(mult b a)
;mult_assoc:forall a b c:S,
eq(mult(mult a b)c)(mult a(mult b c))
;mult_unity_a:forall a:S,eq(mult unity a)a
;mult_zero_a:forall a:S,eq(mult zero a)zero
;mult_inv_a:forall a:S,~(eq a zero)->eq(mult (inv a)a)unity
;distr:forall a b c:S,
eq(mult a(add b c))(add (mult a b)(mult a c))
}.
Definition A:(Field Q Qplus Qopp Qmult Qinv  1 0 Qeq).
split.
intros.
apply (Qplus_comm a b).
intros;rewrite<- Qplus_assoc;reflexivity.
intros;apply Qplus_0_l.
intros;rewrite (Qplus_comm (-a) a);apply Qplus_opp_r.
intros;apply Qmult_comm.
intros;rewrite Qmult_assoc;reflexivity.
intros;apply Qmult_1_l.
intros;apply Qmult_0_l.
intros;rewrite Qmult_comm;apply Qmult_inv_r;apply H.
intros;apply Qmult_plus_distr_r.
Qed.
Add LoadPath ".".
Require Import Group.
Require Import .
Definition QM(a:(A)):Group .

