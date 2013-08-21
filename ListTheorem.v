Require Import List.

Check nth_error.
Check Exc.
Print Exc.
Print option.

Theorem nth_incl:forall {A} xs (x:A),
In x xs<->exists i,Some x=nth_error xs i.
intros.
split.
elim xs.
intros  H0;destruct H0.
intros.
destruct H0.
exists 0.
simpl.
rewrite H0.
reflexivity.

destruct H.
exact H0.
exists (S x0).
simpl.
exact H.
elim xs.
intro.
destruct H.
case_eq x0.
intros.
rewrite H0 in H.
simpl in *.
discriminate.
intros.
rewrite H0 in H.
simpl in H.
discriminate.
intros.
destruct H0.
simpl in *.
case x0 in *.
simpl in *.
injection H0.
intro H1;left;symmetry;exact H1.
simpl in *.
right;apply H.
exists x0;exact H0.
Qed.




