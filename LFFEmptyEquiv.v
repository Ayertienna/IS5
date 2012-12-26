Require Export LFFPPermutLib.

Fixpoint emptyEquiv (G: list (list (var * ty))) :=
match G with
| nil => nil
| a::G' => (@nil (var * ty)) :: emptyEquiv G'
end.

Lemma emptyEquiv_permut_empty:
forall G G',
  G ~=~ emptyEquiv G' ->
  forall C, Mem C G -> C = nil.
Admitted.

Lemma double_emptyEquiv:
forall G,
 emptyEquiv G = emptyEquiv (emptyEquiv G).
Admitted.
