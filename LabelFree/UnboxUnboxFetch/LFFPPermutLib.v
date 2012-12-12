Require Export PermutLib.
Require Export Shared.

Open Scope permut_scope.

Inductive PPermut: list ctx_LF -> list ctx_LF -> Prop :=
| PPermut_nil: PPermut nil nil
| PPermut_skip: forall G G' A A',
  A *=* A' -> PPermut G G' -> PPermut (A::G) (A'::G')
| PPermut_swap: forall G A A' B B',
  A *=* A' -> B *=* B' -> PPermut (A::B::G) (A'::B'::G)
| PPermut_trans: forall G G' G'',
  PPermut G G' -> PPermut G' G'' -> PPermut G G''
.

Notation "G ~=~ G'" := (PPermut G G') (at level 70).
