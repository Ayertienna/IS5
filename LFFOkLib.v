Require Export LFFPPermutLib.

Inductive ok_LF {A}: list (prod var A) -> list var -> Prop :=
| Ok_nil: forall U, ok_LF nil U
| Ok_step: forall G T w U,
  ~ Mem w U -> ok_LF G (w::U) -> ok_LF ((w, T)::G) U
.

Definition ok_Bg (G: bg_LF) : Prop := ok_LF (concat G) nil.

Definition used_vars_ctx_LF (L: bg_LF) :=
  map fst (concat L).

Lemma ok_Bg_PPermut:
forall G G',
  ok_Bg G -> G ~=~ G' -> ok_Bg G'.
Admitted.

Lemma ok_Bg_fresh:
forall G Gamma x A,
  ok_Bg (Gamma::G) ->
  ~ Mem x (used_vars_ctx_LF (Gamma::G)) ->
  ok_Bg (((x, A) :: Gamma)::G).
Admitted.

Lemma ok_Bg_nil:
forall G,
  ok_Bg G ->
  ok_Bg (nil::G).
Admitted.

Hint Resolve ok_Bg_nil.
