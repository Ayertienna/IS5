Require Export LFFPPermutLib.

Inductive ok_LF {A}: list (prod var A) -> list var -> Prop :=
| Ok_nil: forall U, ok_LF nil U
| Ok_step: forall G T w U,
  ~ Mem w U -> ok_LF G (w::U) -> ok_LF ((w, T)::G) U
.

Definition ok_Bg (G: bg_LF) : Prop := ok_LF (concat G) nil.
