Inductive term: Set :=
| zero: term
| succ: term -> term
| add: term -> term -> term
| mul: term -> term -> term.

Fixpoint nat_term (n: nat): term :=
  match n with
  | 0 => zero
  | S m => succ (nat_term m)
  end.

Variable teq: term -> term -> Prop.

Axiom am0: forall x, add x zero = x.

Axiom ams: forall x y, add x (succ y) = succ (add x y).

Theorem add_nat: forall m n, add (nat_term m) (nat_term n) = nat_term (n + m).
                               intros m.
                               induction n.
                               rewrite am0.
                               reflexivity.
                               simpl.
                               rewrite ams.
                               rewrite IHn.
                               reflexivity.
Qed.

