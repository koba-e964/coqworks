Require Import List.

Section PropLogic.

Inductive PP:Type:=
|axiom:nat->PP
|bottom:PP
|conj:PP->PP->PP
|cond:PP->PP->PP (* conditional ,A->B*)
|disj:PP->PP->PP (* disjunction, a or B *)
|neg:PP->PP.

Search list.
SearchPattern (list _->Prop).
Check In.
Print In.
Infix  "&":=conj (at level 70).
Infix "or":=disj (at  level 80).
Infix "-->":=cond (at level 90).




(*Inductive provable:list PP->PP->Prop:=
|taut A:forall prec,
In A prec->provable prec A
|conj_intro A B:forall prec:list PP,
In A prec->In B prec->provable prec (A&B)
|conj_elim_l A B:forall prec:list PP,
In (A&B) prec->provable prec A 
|conj_elim_r A B:forall prec:list PP,
In (A&B) prec->provable prec B 
|cond_intro A B C:
(forall prec,In A prec->In B prec->provable prec C)->forall prec:list PP,In A prec->provable prec (B-->C)
|cond_elim A B:
forall prec:list PP,
In A prec->In (A-->B) prec->provable prec B
|disj_intro_l A B:forall prec:list PP,
In A prec->provable prec (A or B)
|disj_intro_r A B:forall prec:list PP,
In B prec->provable prec (A or B)
|disj_elim A B C:
(forall prec,In A prec->provable prec C)->
(forall prec,In B prec->provable prec C)->
(forall prec,In (A or B) prec->provable prec C)
|bottom_intro A:forall prec:list PP,
provable prec A->provable prec (neg A)->provable prec bottom
|neg_intro A:forall prec:list PP,
provable (A :: prec) bottom->provable prec (neg A).*)

Axiom (provable:PP->PP->Prop).
Axiom (taut :forall A,provable A (A-->A)).
Axiom (conj_intro:forall A B,provable A (A&B)).
|conj_elim_l A B:forall prec:list PP,
In (A&B) prec->provable prec A 
|conj_elim_r A B:forall prec:list PP,
In (A&B) prec->provable prec B 
|cond_intro A B C:
(forall prec,In A prec->In B prec->provable prec C)->forall prec:list PP,In A prec->provable prec (B-->C)
|cond_elim A B:
forall prec:list PP,
In A prec->In (A-->B) prec->provable prec B
|disj_intro_l A B:forall prec:list PP,
In A prec->provable prec (A or B)
|disj_intro_r A B:forall prec:list PP,
In B prec->provable prec (A or B)
|disj_elim A B C:
(forall prec,In A prec->provable prec C)->
(forall prec,In B prec->provable prec C)->
(forall prec,In (A or B) prec->provable prec C)
|bottom_intro A:forall prec:list PP,
provable prec A->provable prec (neg A)->provable prec bottom
|neg_intro A:forall prec:list PP,
provable (A :: prec) bottom->provable prec (neg A).*)


Definition absurdity:=forall prec B,
In bottom prec->provable prec B.
Definition disj_syll:Prop:=forall A B:PP,
forall prec:list PP,
In (A or B) prec->In (neg A) prec->provable prec B.
Lemma asurd_disj_syll_iff:
absurdity<->disj_syll.
unfold absurdity,disj_syll.
split.
intros.
apply (disj_elim A B).
intros.
apply H.
apply bottom_intro.
intro.
intros.








