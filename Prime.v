Require Import ZArith.
Require Import Arith.
Require Import Coq.Program.Wf.
Require Import Bool.
Check shift.
Print shift.

Print Zmod.
Print Zdiv_eucl.
Print Zdiv_eucl_POS.

Eval compute in (Zdiv_eucl_POS 22%positive (7%Z)).
Print Z_of_nat.

Print P_of_succ_nat.
Print Psucc.
Print Zpos.

Print prod.

Definition natmod_inc(x y:nat):nat:=
if beq_nat (S x) y then 0 else S x.

Fixpoint  natmod_1(x y:nat):=match x with 
|0=>0
|S x'=>natmod_inc(natmod_1 x' y)y
end.
Definition natmod(x y:nat):nat:=
match y with
|O=>x
|S _=>natmod_1 x y
end.

Theorem natmod_lt_denom:
forall a b:nat,
natmod a (S b)<S b.
intros.
elim a.
compute.
Check le_n_S.
Check le_0_n.
apply le_n_S.
exact (le_0_n b).

intros.
simpl.
unfold lt.
unfold lt in H.
apply le_S_n in H.
apply le_n_S.
assert (forall m b:nat,m<=b->natmod_inc m (S b)<=b).
intros.
unfold natmod_inc.
simpl.
assert (m<b0\/ m=b0).
Check le_lt_or_eq.
exact (le_lt_or_eq m b0 H0).
elim H1.
intro.
SearchAbout(beq_nat _ _=true).
Lemma lt_neq: (forall x y:nat,x<y->x<>y).
intros.
unfold lt in H.
intro.
rewrite H0 in H.
exact (le_Sn_n y H).
Defined.
generalize H2;intro.
apply lt_neq in H2.

Check not_true_is_false.
Check beq_nat_true_iff.
rewrite <-beq_nat_true_iff in H2.
apply not_true_is_false in H2.
rewrite H2.
apply H3.
intro.
apply beq_nat_true_iff in H2.
rewrite H2.
exact (le_0_n b0).

apply H0.
apply H.
Defined.

Infix "mod":=natmod (at level 40).


Fixpoint  natdiv_1(x y:nat):=match x with 
|0=>0
|S x'=>
(if (beq_nat (natmod_1 x y) 0) then 1 else 0)
+natdiv_1 x' y
end.


Definition natdiv(x y:nat):nat:=
match y with
|0=>0
|S _=>
natdiv_1 x y end.

Eval compute in natdiv 9 3.

Infix "div":=natdiv (at level 40).


Lemma lt_natmod_1_fixed:
forall x m:nat,
x<S m->natmod_1 x (S m)=x.
induction x.
intros.
reflexivity.
intros.
generalize H;intro.
apply lt_neq in H.
unfold natmod in *.
unfold natmod_1.
rewrite IHx.
unfold natmod_inc.
rewrite <-beq_nat_true_iff in H.
apply not_true_is_false in H.
rewrite H.
reflexivity.
apply lt_S.
apply lt_S_n.
exact H0.
Defined.
Theorem lt_natmod_fixed:
forall x m:nat,
x<S m->natmod x (S m)=x.
intros.
apply lt_natmod_1_fixed.
exact H.
Defined.



Lemma natmod_double:
forall x y:nat,
(x mod y)=((x mod y)mod y).
intros.
case y.
assert (forall x:nat,natmod x 0=x).
intros.
reflexivity.
unfold natmod.
reflexivity.
intros.
symmetry.
apply lt_natmod_fixed.
apply natmod_lt_denom.
Defined.

Theorem natmod_div:
forall x m:nat,
x=(x mod m)+(x div m)*m.
intros.
case m.
simpl.
rewrite plus_comm.
reflexivity.
intros.
elim x.
simpl;reflexivity.
simpl.
intros.
simpl.
Lemma natmod_div_1:
forall x y:nat,
((if beq_nat x 0 then 1 else 0)*y+x)=
(if beq_nat x 0 then x+y else x).
intros.
generalize (beq_nat x 0).
induction b.
simpl.
rewrite plus_comm.
rewrite (plus_comm y 0).
simpl;reflexivity.
simpl;reflexivity.
Defined.
rewrite mult_plus_distr_r.
rewrite plus_assoc.
rewrite (plus_comm (natmod_inc(natmod_1 n0(S n))(S n)) _ ).
rewrite natmod_div_1.

Lemma natmod_div2:
forall x y:nat,
let r :=(natmod_inc x (S y)) in
(if beq_nat r 0 then r+(S y) else r)=S x.
intros.
unfold natmod_inc in r.
simpl in r.
generalize (refl_equal (beq_nat x y)).
intro.
case (beq_nat x y) in r, H at 2.
simpl.
symmetry.
apply eq_S.
apply beq_nat_true.
exact H.
info reflexivity.
Defined.
rewrite (natmod_div2 (natmod_1 n0 (S n)) n).
simpl.
rewrite <-H.
reflexivity.
Defined.

Lemma natmod_period_1:
forall x y:nat,
(x+(S y))mod (S y)=x mod (S y).
intros.
elim x.
simpl.
rewrite lt_natmod_1_fixed.
unfold natmod_inc.
simpl.
generalize (refl_equal y);intro.
rewrite <-beq_nat_true_iff in H.
rewrite H.
reflexivity.
apply le_n.
intros.
simpl in *.
rewrite H.
reflexivity.
Defined.



Theorem natmod_period:
forall x y z,(x+z*y)mod y=x mod y.
intros.
case y.
simpl.
rewrite mult_comm.
rewrite plus_comm.
reflexivity.
intro.
elim z.
simpl.
rewrite plus_comm.
reflexivity.
intros.
cut (x+S n0*S n=x+n0*S n+S n).
intros.
rewrite H0.
rewrite (natmod_period_1 (x+n0*S n) n).
exact H.
simpl.
rewrite<-plus_assoc.
rewrite (plus_comm (n0*S n)).
reflexivity.
Defined.

Theorem natmod_additive:
forall x y m:nat,
(x+y)mod m=((x mod m)+(y mod m))mod m.
intros.
rewrite (natmod_div x m).
rewrite (natmod_div y m).
rewrite plus_assoc.
rewrite natmod_period.
rewrite <-plus_assoc.
rewrite (plus_comm _ (y mod m)).
rewrite plus_assoc.
repeat rewrite natmod_period.
repeat rewrite <-natmod_double.
reflexivity.
Defined.

Require Import Recdef.


Function euclid(x:nat)(y:nat){measure (fun x=>x)x}:nat:=
match x with
|0=>y
|S x'=>(euclid (natmod y x) x)
end.
intros.
apply natmod_lt_denom.
Defined.


Lemma euclid_calc:
forall x y:nat,
(euclid (S x) y =euclid (y mod (S x))(S x)).
intros.
simpl.
Admitted.
Print euclid_calc.

Lemma euclid_calc_0:
forall y:nat,
euclid 0 y=y.
intro.
unfold euclid.
unfold euclid_terminate.
simpl.
reflexivity.
Qed.


Lemma natmod_0_n:
forall n:nat,
0 mod n=0.
intro n;case n.
reflexivity.
reflexivity.
Defined.


Definition divisible(d x:nat):Prop:=
exists b:nat,b*d=x.

Infix "|":=divisible (at level 20).

Definition divisible_b(d x:nat):bool:=
beq_nat (natmod x d)0.
Theorem divisible_pb:
forall d x:nat,
divisible d x<->divisible_b d x=true.
unfold divisible,divisible_b.
intros.

split.
intro.
destruct H.
rewrite <-H.
cut (x0*d=0+x0*d).
intro.
rewrite H0.
rewrite (natmod_period 0 d x0).
rewrite natmod_0_n.
reflexivity.
reflexivity.
rewrite (natmod_div x d).
rewrite natmod_period.
intro.
rewrite beq_nat_true_iff in H.
rewrite <-natmod_double in H.
rewrite H.
simpl.
exists (x div d).
reflexivity.
Defined.

Definition comm_div(g x y:nat):Prop:=
divisible g x/\divisible g y.
Definition is_gcd(g x y:nat):Prop:=
forall d:nat, comm_div d x y<->divisible d g.
Eval lazy in divisible_b 2 4.


Check le_ind.
Lemma gcd_is_comm_div:
forall g x y:nat,
is_gcd g x y->comm_div g x y.
intros.
rewrite (H g).
exists 1.
simpl.
apply plus_comm.
Defined.

Lemma divisible_antisym:
forall a b:nat,
divisible a b->divisible b a->a=b.
intro a.
case a.
intros.
destruct H.
rewrite mult_comm in H.
simpl in *.
exact H.
intros.
destruct H.
destruct H0.
Check mult_is_one.
rewrite <-H in H0.
rewrite mult_assoc in H0.

Print mult.
SearchAbout mult.
assert (forall x n:nat,x*S n=S n->x=1).
intro.
elim x1.
intros.
discriminate.
induction n0.
intros.
reflexivity.
intros.
simpl in H2.
injection H2;intros.
replace (n1 + S (n1 + n0 * S n1)=n1) with (n1 + S (n1 + n0 * S n1)=n1+0)  in H3 .

apply (plus_reg_l (S (n1+n0*S n1)) 0 n1) in H3.
symmetry in H3.
apply O_S in H3.
elim H3.
rewrite (plus_comm n1 0).
reflexivity.
apply H1 in H0.
apply mult_is_one in H0.
destruct H0.
rewrite H2 in H.
simpl in *.
rewrite <-H.
rewrite plus_comm.
reflexivity.
Defined.

Lemma divisible_n_n:
forall n:nat,
n|n.
intros.
exists 1.
apply plus_comm.
Qed.
Lemma divisible_n_0:
forall n:nat,
n|0.
intro;exists 0;auto.
Qed.
Lemma divisible_trans:
forall x y z:nat,
x|y->y|z->x|z.
intros.
destruct H,H0.
exists (x1*x0).
rewrite <-mult_assoc.
rewrite H.
exact H0.
Qed.



Theorem gcd_eucl:
forall x y h:nat,
(is_gcd h x y<->euclid x y=h).
intro x;case x.
Lemma gcd_eucl_1:
forall y h : nat, is_gcd h 0 y <-> euclid 0 y = h.
intros.
split.
intro.
compute.
unfold is_gcd in *.
unfold comm_div in *.
apply divisible_antisym.
destruct (H y).
apply H0.
split.
exists 0;auto.
exists 1;simpl;rewrite plus_comm;reflexivity.
destruct (H h).
apply H1.
exists 1;simpl;rewrite plus_comm;reflexivity.
intros.
rewrite euclid_calc_0 in H.
rewrite H.
unfold is_gcd.
unfold comm_div.
intros.
split.
tauto.
intros.
split.
apply divisible_n_0.
auto.
Qed.
intros.
apply gcd_eucl_1.

intro n.
apply (lt_wf_ind n).
intros.
rewrite euclid_calc.
case_eq (y mod S n0).
intros.
rewrite <-beq_nat_true_iff in H0.
rewrite <-(divisible_pb (S n0) y) in H0.
rewrite euclid_calc_0.
unfold is_gcd.
unfold comm_div.
split.
intros.
apply divisible_antisym.
destruct (H1 (S n0)).
apply H2.
split.
apply divisible_n_n.
auto.
destruct (H1 h).
apply H3.
exact (divisible_n_n h).


intro.
intros.
split.
intros.
rewrite <-H1;apply H2.
intros.
rewrite <-H1 in H2.
split.
auto.
exact (divisible_trans d (S n0) y H2 H0).
intros.
rewrite <-H.
generalize (refl_equal y).
rewrite (natmod_div _ (S n0))at 2.
intro.
rewrite H0 in H1.
rewrite H1.
unfold is_gcd.
unfold comm_div.
split.
intros.
rewrite <-(H2 d).
split.
intro.
split.
apply H3.
destruct H3.
destruct H3,H4.
exists (x0+(y div S n0)*x1).
rewrite mult_plus_distr_r.
rewrite H3.
rewrite <-mult_assoc.
rewrite H4.
reflexivity.
split.
destruct H3.
destruct H3,H4.
exists (x1-(y div S n0)*x0).
rewrite mult_minus_distr_r.
rewrite H4.
rewrite <-mult_assoc.
rewrite  H3.
rewrite plus_comm.
rewrite minus_plus.
reflexivity.
exact (proj1 H3).
intros.
split.
intros.
apply H2.
destruct H3.
split.
destruct H3,H4.
exists (x1-(y div S n0)*x0).
rewrite mult_minus_distr_r.
rewrite H4.
rewrite <-mult_assoc.
rewrite  H3.
rewrite plus_comm.
rewrite minus_plus.
reflexivity.
exact H3.
intro.
rewrite <-H2 in H3.
split.
exact (proj2 H3).
destruct H3.
destruct H3,H4.
exists (x0+(y div S n0)*x1).
rewrite mult_plus_distr_r.
rewrite H3.
rewrite <-mult_assoc.
rewrite H4.
reflexivity.
apply lt_S_n.
rewrite <-H0.
apply natmod_lt_denom.
Qed.





