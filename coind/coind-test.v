(* http://www.cse.chalmers.se/research/group/logic/TypesSS05/Extra/bertot_sl2.pdf *)
CoInductive Llist (A:Set) : Set :=
Lnil : Llist A
| Lcons : A -> Llist A -> Llist A.

CoFixpoint lones : Llist nat := Lcons _ 1 lones.

CoInductive stream (A:Set) : Set :=
  Cons : A -> stream A -> stream A.
Definition Llist_decompose (A:Set)(l:Llist A) : Llist A :=
  match l with
    Lnil => Lnil A
  | Lcons a tl => Lcons _ a tl
  end.
Implicit Arguments Llist_decompose.

Theorem Llist_dec_thm :
  forall (A:Set)(l:Llist A), l = Llist_decompose l.
                               intros A l.
                               case l.
                               trivial.
                               simpl.
                               auto.
Qed.
