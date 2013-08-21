Require Import Arith.

Inductive fin:nat->Type:=
|zero:forall n,fin n
|next:forall n,fin n->fin(S n).

Fixpoint value{n}(f:fin n):nat:=
match f with
|zero m=>0
|next m g=>S(value g)
end.

Print value.

Theorem limited:forall n:nat,
forall f:fin n,
value f<=n.
intro.
intros.
elim f.
unfold value.
intro;apply le_0_n.
intros.
simpl.
exact (le_n_S (value f0) n0 H).
Qed.


Goal forall n:nat,exists f:fin n,value f=n.
intros.
elim n.
exists (zero 0).
auto.
intros.
destruct H.
exists (next n0 x).
simpl.
rewrite H.
reflexivity.
Qed.


Lemma Tmp0:forall p q r:Prop,
(p->q->r)<->(p/\q->r).
intros.
split.
intros.
destruct H0.
apply (H H0 H1).
intros.
exact (H (conj H0 H1)).
Qed.
Print Tmp0.
Print iff.
Print conj.
Print or.
Check nat.
Print nat.
Check le_n_S.
Print le_n_S.

Lemma Tmp1:forall p q r:Prop,
(p/\q->r)->p->q->r.
intros p q r.
rewrite <-Tmp0.
auto.
Qed.
Search iff.
SearchPattern (forall x,x<->x).
Check iff_refl.
Check iff_sym.
Print iff_sym.
Print iff_trans. 

