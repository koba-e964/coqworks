Inductive Ty: Set :=
  ty_o: Ty | ty_arr: Ty -> Ty -> Ty.

Inductive Con: Set :=
  con_empty: Con | con_cons: Con -> Ty -> Con.

Inductive Var: Con -> Ty -> Set :=
  | var_zero: forall g s, Var (con_cons g s) s
  | var_suc: forall g t s, Var g s -> Var (con_cons g t) s.

Inductive Tm: Con -> Ty -> Set :=
  | tm_var: forall g s, Var g s -> Tm g s
  | tm_app: forall g s t, Tm g (ty_arr s t) -> Tm g s -> Tm g t
  | tm_lam: forall g s t, Tm (con_cons g s) t -> Tm g (ty_arr s t).