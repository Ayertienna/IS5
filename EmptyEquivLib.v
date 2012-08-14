(* THIS IS NOT TO BE USED JUST YET *)

Require Import Shared.
Require Import LibList.
Require Import PPermutLib.
Require Import Relations.

Open Scope permut_scope.

(* emptyEquiv = map (fun x => (x, nil)) (map fst G) *)
Fixpoint emptyEquiv (G: Background_LF) : Background_LF :=
match G with
| nil => nil
| (w, a)::G => (w, nil) :: emptyEquiv G
end.

Add Morphism emptyEquiv : Permut_emptyEquiv.
Admitted.

Lemma emptyEquiv_last_change:
forall G G' w C C',
  G  ~=~ G'& (w, C) ->
  emptyEquiv G ~=~ emptyEquiv (G' & (w, C')).
Admitted.

Lemma emptyEquiv_rewrite:
forall G H,
  emptyEquiv (G++H) = emptyEquiv G ++ emptyEquiv H.
Admitted.

Lemma emptyEquiv_rewrite_last:
forall G C,
  emptyEquiv (G & C) = emptyEquiv G ++ emptyEquiv (C::nil).
Admitted.

Lemma emptyEquiv_permut_empty:
forall G G' w,
  G ~=~ emptyEquiv G' ->
  forall C, Mem (w, C) G -> C = nil. 
Admitted.

Lemma double_emptyEquiv:
forall G,
 emptyEquiv G = emptyEquiv( emptyEquiv G).
Admitted.

Lemma emptyEquiv_permut_split_last:
forall G C H,
  G & C ~=~ emptyEquiv H ->
  emptyEquiv G = G.
Admitted.

Lemma emptyEquiv_ok:
forall G,
  ok_Bg G ->
  ok_Bg (emptyEquiv G).
Admitted.