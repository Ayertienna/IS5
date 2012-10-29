Require Import LLSyntax.
Require Import PermutLib.

Open Scope permut_scope.

Fixpoint ok_Gamma (G: Context_L) (Used: list var) : Prop :=
match G with
| nil => True
| (w, (v, A)) :: G' => ~ Mem v Used /\ ok_Gamma G' (v::Used)
end.

Fixpoint ok_Omega (L: list var) : Prop :=
match L with
| nil => True
| l :: L' => ~ Mem l L' /\ ok_Omega L'
end.

Lemma ok_Gamma_permut:
forall G1 G2 U,
  G1 *=* G2 -> ok_Gamma G1 U -> ok_Gamma G2 U.
Admitted.

Lemma ok_Omega_permut:
forall O1 O2,
  O1 *=* O2 -> ok_Omega O1 -> ok_Omega O2.
Admitted.

Definition ok_L Omega Gamma := ok_Omega Omega /\ ok_Gamma Gamma nil.

Lemma ok_L_permut:
forall O O' G G', O *=* O' -> G *=* G' -> ok_L O G -> ok_L O' G'.
intros; destruct H1; split;
[eapply ok_Omega_permut | eapply ok_Gamma_permut]; eauto.
Qed.

Lemma ok_L_extend_fresh:
forall O G x w A,
  ok_L O G ->
  x \notin used_vars_context_L G ->
  ok_L O ((w, (x, A))::G).
Admitted.

Lemma ok_L_smaller:
forall O G x w A,
  ok O ((w, (x, A))::G) -> ok O G.
Admitted.

Lemma ok_L_Mem_contradiction:
  Mem (w, (x, A)) Gamma ->
  ok_L Omega ((w, (x, B)) :: Gamma) ->
  False.
Admitted.