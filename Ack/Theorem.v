Require Import Definitions.
Require Import Arith.
Lemma ack_0x_fst:forall x y,
ack 0 y<=ack x y.
induction x.
auto.
induction y.
change (1<=ack x 1).
apply (le_trans _ 2 _).
auto.
apply IHx.
change (ack 0(S y)<=ack x(ack(S x)y)).
apply (le_trans _ (ack 0(ack (S x)y))_).
apply le_n_S.
apply IHy.
apply IHx.
Qed.
Lemma ack_0x_fst_lt:forall x y,
ack 0 y<ack (S x) y.
induction x.
induction y.
auto.
change (ack 0 (S y)<ack 0 (ack 1 y)).
apply le_n_S.
apply IHy.
intros.
elim y.
change(ack 0 0<(ack(S x)1)).
apply (le_trans _ 3 _).
auto.
apply (IHx 1).
intros.
change (ack 0(S n)<ack (S x)(ack(S(S x))n)).
apply (lt_trans _ ((ack 0(ack (S (S x))n)))_).
repeat apply le_n_S.
apply (H).
apply IHx.
Qed.

Lemma ack_incr_snd:forall x y1 y2,
y1<=y2->ack x y1<=ack x y2.
induction x.
intros.
apply le_n_S.
exact H.
intros.
elim H.
auto.
intros.
change (ack (S x) y1<=ack x (ack (S x)m)).
apply (le_trans _ (S(ack(S x)m))_).
apply (le_S _ _ H1).
apply ack_0x_fst.
Qed.

Lemma ack_incr_snd_lt:forall x y1 y2,
y1<y2->ack x y1<ack x y2.
induction x.
intros.
apply le_n_S.
exact H.
intros.
elim H.
change(ack (S x) y1 < ack x(ack(S x)y1)).
apply ack_0x_fst.
intros.
change (ack (S x) y1<ack x (ack (S x)m)).
apply (le_trans _ (S(ack(S x)m))_).
apply (le_S _ _ H1).
apply ack_0x_fst.
Qed.


Lemma ack_S_fst_lt:forall x y1 y2,
y1<=y2->ack x y1<ack (S x) y2.
intros x y1 y2.
intros.
elim H.
case y1.
change(ack x 0<ack x 1).
apply ack_incr_snd_lt.
auto.
intros.
change (ack x (S n)<ack x(ack (S x) n)).
apply ack_incr_snd_lt.
apply ack_0x_fst_lt.
intros.
apply (le_trans _ (S(ack(S x)m)) _ 
(le_S _ _ H1)).
change (ack 0(ack(S x)m)<=ack x(ack(S x)m)).
apply (ack_0x_fst x (ack (S x) m)).
Qed.




Lemma ack_incr:forall x1 x2 y1 y2:nat,
x1<=x2->y1<=y2->ack x1 y1<=ack x2 y2.
intros.
apply (le_trans _ (ack x1 y2) _).
apply ack_incr_snd.
apply H0.
elim H.
auto.
intros.
apply (le_trans _(ack m y2)_).
auto.
apply le_S_n.
apply lt_S.
apply ack_S_fst_lt.
auto.
Qed.
Check lt_S.
Print lt_S.

Lemma ack_mov:forall a m n:nat,
ack m (n+a)<=ack(a+m) n.
induction a.
intros.
rewrite plus_comm.
apply le_n.
intros.
elim n.
apply (IHa m 1).
intros.
simpl.
rewrite plus_comm.
simpl.
rewrite plus_comm.
change (ack m (S(S(n0+a)))<=
ack (a+m)(ack (S(a+m)) n0)).
apply (le_trans _ (ack (a+m) (S(S n0)))).
apply (IHa m (S(S n0))).
apply ack_incr_snd.
apply (le_trans _ (ack m (n0+S a))).
change (ack 0 (S n0) <= ack m (n0 + S a)).
apply ack_incr.
apply le_0_n.
rewrite plus_comm.
apply le_n_S.
apply le_plus_r.
apply H.
Qed.



Program Fixpoint fin_sum{n:nat}
(arg:fin n->nat){struct n}:nat:=
match n with
|0=>0
|S n'=>(hd (_:fin(S n')->nat))+(fin_sum (_:fin n'->nat))
end.
Obligation 1.
apply arg.
apply F0.
Defined.
Obligation 2.
Check tl.
apply (tl (n:=n')) in arg.
apply arg.
exact H.
Defined.
Print fin_sum.
Print fin_sum_obligation_1.
Eval compute in fin_sum (fun i:fin 2=>if i then 2 else 1).
Goal forall n,
forall arg:fin (S n)->nat,
fin_sum arg=(hd arg)+(fin_sum (tl arg)).
intros.
simpl.
unfold fin_sum_obligation_2.
unfold fin_sum_obligation_1.
simpl.
reflexivity.
Qed.


Program Fixpoint fin_max{n:nat}
(arg:fin n->nat){struct n}:nat:=
match n with
|0=>0
|S n'=>
((arg (_)):nat)+(fin_max (_:fin n'->nat))
end.
Obligation 1.
left.
exact tt.
Defined.
Obligation 2.
apply tl in arg.
apply arg.
apply H.
Defined.
Eval compute in fin_max (fun i:fin 2=>if i then 1 else 0).


Definition fin_max_max:forall n:nat,
forall arg:fin n->nat,
forall i:fin n,
(arg i<=fin_max arg).
induction n.
simpl.
intros.
induction i.
intros.
generalize (IHn (tl arg));intro.
simpl.
case i.
intro;case u;clear u.
apply le_plus_trans.
auto.
intros.
unfold fin_max_obligation_2.
simpl.
fold fin in f.
rewrite plus_comm.
apply le_plus_trans.
apply H.
Defined.

Theorem fin_sum_upp:forall n:nat,
forall arg:fin n->nat,
forall i:fin n,
arg i<=fin_sum arg.
induction n.
intros.
case i.
intros.
simpl.
unfold fin_sum_obligation_1,fin_sum_obligation_2.
simpl.
case i.
intros.
case u.
apply le_plus_l.
intros.
apply (le_trans _ (fin_sum (tl arg))).
apply IHn with (arg:=tl arg).
apply le_plus_r.
Qed.

Definition tot_le{n}(a b:fin n->nat):Prop:=
forall i:fin n,
a i<= b i.
Theorem tot_le_prim_le:forall n:nat,
forall f:prim_rec n,
forall a b:fin n->nat,
tot_le a b->eval f a<=eval f b.
fix IHf 2.
intros n f.
generalize (refl_equal n).
refine match f as ff in prim_rec nn return 
n=nn->forall a b:fin nn->nat,tot_le a b->eval ff a <= eval ff b
with
    | pr_proj n i => _
    | pr_succ => _
    | pr_const n k => _
    | pr_compose m n fs g => _
    | pr_primrec n f g => _
end.

 intros.
 simpl.
 apply (H0 i).

 intros.
 simpl.
 apply le_n_S.
 apply H0.

 intros.
 simpl.
 auto.

 intros.
 simpl.
 apply IHf.
 unfold tot_le.
 intros.
 apply IHf.
 exact H0.
Guarded.

 intros.
 unfold eval.
 fold eval.
 case (a F0).
 case (b F0).
 apply IHf.
 unfold tot_le.
 intro.
 compute.
 apply H0.
 intros.
 simpl.
Abort.
Lemma tot_le_fin_sum:forall n:nat,
forall a b:fin n->nat,
tot_le a b->fin_sum a<=fin_sum b.
induction n.
compute.
auto.
intros.
change ((hd a)+(fin_sum (tl a))<=(hd b)+(fin_sum (tl b))).
apply plus_le_compat.
apply H.
apply IHn.
intro.
apply H.
Qed.
Lemma ack_1_n:forall n:nat,
ack 1 n=S(S n).
induction n.
auto.
change (ack 0 (ack 1 n)=S(S(S n))).
rewrite IHn.
auto.
Qed.

Lemma ack_2_n:forall n:nat,
ack 2 n=2*n+3.
induction n.
auto.
change (ack 1 (ack 2 n)=2*S n+3).
rewrite ack_1_n.
rewrite IHn.
ring.
Qed.


Lemma ack_twice_le:forall x,
3<=x->forall y:nat,
2*ack x y<=ack x (S y).
intro x.
case x.
intros.
apply le_Sn_0 in H.
case H.
intros.
change (2*ack(S n)y<=ack n(ack(S n)y)).
apply le_S_n in H.
apply (le_trans _ (ack 2(ack(S n)y))).
rewrite ack_2_n.
apply le_plus_l.
apply ack_incr.
exact H.
apply le_n.
Qed.




Lemma ack_mult:forall x,
3<=x->
forall m y,
(S m)*ack x y<=ack x (y+m).
intros x H m.
elim m.
intros.
rewrite plus_0_r.
rewrite mult_1_l.
apply le_n.
intros.
rewrite<-plus_n_Sm.
apply (le_trans _ (2*(ack x (y+n)))).
apply (le_trans _ (2*(S n*ack x y))).
rewrite mult_assoc.
apply mult_le_compat_r.
elim n.
apply le_n.
intros.
simpl in *.
repeat apply le_n_S.
repeat apply le_S_n in H1.
rewrite (plus_comm n0 )in *.
apply le_S.
apply H1.
apply mult_le_compat_l.
apply H0.
apply ack_twice_le.
exact H.
Qed.


Lemma pile_ack:
forall n:nat,
forall xs:fin n->nat,
{mc:nat|
forall c,
fin_sum (fun i : fin n => ack (xs i)c)
<=n*ack mc c}.
induction n.
intros.
exists 0.
intros.
simpl.
apply le_0_n.

intros.
destruct (IHn (tl xs)).
exists (x+(xs F0)+3).
simpl.
unfold fin_sum_obligation_1,
fin_sum_obligation_2.
simpl.
unfold hd.
unfold tl.
intro.
apply plus_le_compat.
apply ack_incr.
rewrite plus_comm.
rewrite plus_assoc.
apply le_plus_r.
apply le_n.
apply (le_trans _ (n*ack x c)).
apply l.
apply mult_le_compat_l.
apply ack_incr.
rewrite <-plus_assoc.
apply le_plus_l.
apply le_n.
Qed.

Lemma tot_le_sum:
forall n:nat,
forall a b:fin n->nat,
tot_le a b->fin_sum a<=fin_sum b.
induction n.
auto.
intros.
simpl.
unfold fin_sum_obligation_1,
fin_sum_obligation_2.
simpl.
unfold hd,tl.
apply plus_le_compat.
apply H.
apply IHn.
intro.
apply H.
Qed.




Theorem ack_is_not_primitive_recursive :

  forall f : prim_rec 2, exists m, exists n,
    eval f (fun i => if i then m else n) <> ack m n.
Lemma wider:
forall a:nat,
forall f:prim_rec a,
{m:nat|
forall arg:fin a->nat,
eval f arg
<ack m (fin_sum arg)}.
fix IHf 2.
intros.
generalize (refl_equal a).
refine match f as ff in prim_rec aa
return aa = a ->
{m : nat|
  forall arg : fin aa->nat,
 eval ff arg < ack m (fin_sum arg)}
with
    | pr_proj n i => _
    | pr_succ => _
    | pr_const n k => _
    | pr_compose m n fs g => _
    | pr_primrec n f g => _
end.
(* pr_proj*)
intros.
simpl.
exists  1.
intros.
apply (le_lt_trans _ (fin_sum arg)).
apply fin_sum_upp.
apply ack_0x_fst.

(* pr_succ *)

intros.
exists 1.
intros.
unfold eval.
change (ack 0 (arg F0)<ack 1(fin_sum arg)).
apply ack_S_fst_lt.
apply fin_sum_upp.

(* pr_const *)

intros.
exists k.
intros.
unfold eval.
elim k.
apply le_n_S.
apply le_0_n.
intros.
apply (lt_le_trans _ (S(ack n0 (fin_sum arg)))).
apply lt_n_S.
apply H0.
apply ack_S_fst_lt.
auto.
Guarded.

(* pr_compose *)

intros.
simpl.
destruct (IHf n g).
Print sig.
generalize (fun i:fin n =>
match IHf _ (fs i) return nat with
|exist m1 _=> m1 end).
intros IHfm.
destruct (pile_ack n (fun i:fin n =>
match IHf _ (fs i) return nat with
|exist m1 _=> m1 end)).
exists (3+x+x0).
intro.
apply (lt_le_trans _ (ack x (fin_sum(fun i:fin n=>eval(fs i)arg))) _).
apply l.
assert(forall i:fin n,
{ci:nat|eval (fs i) arg<=ack ci (fin_sum arg)}).
intros.
destruct(IHf m (fs i)).
exists x1.
apply le_S_n.
apply le_S.
apply l1.
assert ( {cs :fin n-> nat | forall i:fin n,eval (fs i) arg <= ack (cs i) (fin_sum arg)}).
Check exist.
refine (exist (fun i:fin n=>
match (H0 i) with
|exist ci Hi=>_:Prop end) _).
intros.

exists 
simpl.
apply (le_trans _ (
ack x (fin_sum (fun i:fin n
=>ack (match (IHf m (fs i))with
|exist ci _=>ci end) (fin_sum arg))))).
apply ack_incr_snd.
apply tot_le_sum.
intro.
generalize (fs i).
intros.
simpl.
Check falso.
apply (H0 c).
intro.
destruct 
apply IHf.
exists n.




Admitted.
Lemma argv_equal:forall (n:nat),
forall f:prim_rec n,
forall (arg1 arg2:fin n->nat),
(forall i:fin n,arg1 i=arg2 i)->
eval f arg1=eval f arg2.
fix IHf 2.
intros n f.
generalize (refl_equal n).
refine match f as ff in prim_rec nn return nn=n->
forall arg1 arg2:fin nn->nat,(forall i : fin nn, arg1 i = arg2 i) -> eval ff arg1 = eval ff arg2
with
    | pr_proj n i => _
    | pr_succ => _
    | pr_const n k => _
    | pr_compose m n fs g => _
    | pr_primrec n f g => _
end.
simpl.
intros.
apply H0.
simpl.
intros.
rewrite H0.
auto.
simpl.
auto.
simpl.
intros.
Guarded.
apply IHf.
intro.
apply IHf.
apply H0.
Guarded.
intros.
unfold eval.
rewrite (H0 F0).
fold eval.
elim (arg2 F0).
apply (IHf _ _ (tl arg1) (tl arg2)).
unfold tl.
intro.
apply H0.
intros.
rewrite H1.
apply IHf.
intro i;case i.
auto.
intro.
fold fin in *.
case f1.
intro.
reflexivity.
intro.
apply H0.
Qed.

intros.
generalize wider.
intros.
destruct (H 2 f).
exists x.
exists x.
generalize(H0 x (le_n x));intro.
intro.
assert (forall i:fin 2,(fun _ : fin 2 => x)i=(fun i : fin 2 => if i then x else x)i).
intro.
case i;auto.
rewrite <-(argv_equal  _ _ _ _ H3) in H2. 
rewrite H2 in H1.
case (le_Sn_n _ H1).
Qed.
