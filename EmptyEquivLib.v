(* emptyEquiv = map (fun x => (x, nil)) (map fst G) *)
Fixpoint emptyEquiv (G: Background_LF) : Background_LF :=
match G with
| nil => nil
| (w, a)::G => (w, nil) :: emptyEquiv G
end.

Lemma emptyEquiv_ppermut:
forall G G',
  G ~=~ G' ->
  emptyEquiv G ~=~ emptyEquiv G'.
Admitted.

Lemma emptyEquiv_last_change:
forall G G' w C C',
  G  ~=~ G'& (w, C) ->
  emptyEquiv G ~=~ emptyEquiv (G' & (w, C')).
Admitted.

Lemma emptyEquiv_ppermut_rewrite_simple
emptyEquiv G |= ... ->
G ~=~ G' ->
emptyEquiv G' |= ...

Lemma emptyEquiv_ppermut_rewrite:
emptyEquiv G |= .. ->
emptyEquiv G ~=~ G' ->
emptyEquiv G' |= ... 
