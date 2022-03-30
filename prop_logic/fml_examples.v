Load fml.

Goal forall v: fml, fml_not v = v ==> fml_bot.
reflexivity.
Qed.

Goal forall a b: fml, fml_and a b = a and b.
reflexivity.
Qed.

Goal forall a b: fml, fml_or a b = a or b.
reflexivity.
Qed.
