(* Section の練習 *)

Section Poslist.
  (* このセクションの中では、Aが共通の変数として使える。 *)
  Variable A : Type.
  (* 非空なリスト *)
  Inductive poslist : Type := one: A -> poslist
    | cons: A -> poslist -> poslist.

  Section Fold.
    (* 二項演算 *)
    Variable g : A -> A -> A.

   (* gによって畳み込む。
    * 次のどちらかを定義すること。どちらでもよい。
    * 左畳み込み : リスト [a; b; c] に対して (a * b) * c を計算する。
    * 右畳み込み : リスト [a; b; c] に対して a * (b * c) を計算する。
    *)
    Fixpoint fold (l : poslist): A := 
      match l with
        | one x => x
        | cons x y => g x (fold y)
      end.
    (* DefinitionをFixpointなどに置き換えてもよい。 *)
  End Fold.
  Check fold.
End Poslist.
Check fold.
(* Poslistから抜けたことにより、poslistは変数Aについて量化された形になる。 *)

(* このリストに関するmap関数 *)
Section PoslistMap.
  Variable A B : Type.
  Variable f : A -> B.

  Fixpoint map (ls: poslist A): poslist B :=
    match ls with
    | one _ x => one _ (f x)
    | cons _ x y => cons _ (f x) (map y)
    end.
End PoslistMap.

(* 今回は証明すべきことはないので、定義を正確に *)