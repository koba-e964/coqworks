Set Implicit Arguments.

(* A set of propositional variables. *)
Variable ap: Set.

(* Formulae in intuitionistic and propositinal logic. *)
Inductive fml: Set :=
  | fml_var: ap -> fml
  | fml_and: fml -> fml -> fml
  | fml_or: fml -> fml -> fml
  | fml_imp: fml -> fml -> fml
  | fml_bot: fml.

(* Notations.
 * We define level(and) := level( * ) == level(&&), level(or) := level(+) == level(||) and level(==>) slightly lower than +.
 * Since these formulae can't contain arithmetic expressions, there will be no clash.
 *)
Notation "s 'and' t" := (fml_and s t) (at level 40, left associativity).
Notation "s 'or' t" := (fml_or s t) (at level 50, left associativity).
Notation "s ==> t" := (fml_imp s t) (at level 55, right associativity).

Definition fml_not x := x ==> fml_bot.
Definition fml_top := fml_not fml_bot.
