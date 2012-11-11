Require Import LFFSubstitution.
Require Import LFFSyntax.
Require Import LFFOkLib.

Open Scope permut_scope.
Open Scope is5_scope.

Reserved Notation " G  '|=' Gamma '|-' M ':::' A" (at level 70).

Inductive types_LF : bg_LF -> ctx_LF -> te_LF -> ty -> Prop :=

| t_hyp_LF: forall A G Gamma v
  (Ok: ok_Bg (Gamma::G))
  (H: Mem (v, A) Gamma),
  G |= Gamma |- hyp_LF (fte v) ::: A

| t_lam_LF: forall L A B G Gamma M
  (Ok: ok_Bg (Gamma::G))
  (H: forall v, v \notin L -> G |= (v, A)::Gamma |- M ^^ (hyp_LF (fte v)) ::: B),
  G |= Gamma |- lam_LF A M ::: A ---> B

| t_appl_LF: forall A B G Gamma M N
  (Ok: ok_Bg (Gamma::G))
  (H1: G |= Gamma |- M ::: A ---> B)
  (H2: G |= Gamma |- N ::: A),
  G |= Gamma |- appl_LF M N ::: B

| t_box_LF: forall G Gamma M A
  (Ok: ok_Bg (G & Gamma))
  (H: G & Gamma |= nil |- M ::: A),
  G |= Gamma |- box_LF M ::: [*] A

| t_unbox_LF: forall G Gamma M A
  (Ok: ok_Bg (Gamma :: G))
  (H: G |= Gamma |- M ::: [*] A),
  G |= Gamma |- unbox_LF M ::: A

| t_unbox_fetch_LF: forall G Gamma Gamma' M A
  (Ok: ok_Bg (Gamma:: G & Gamma'))
  (H: G & Gamma' |= Gamma |- M ::: [*] A),
  forall G', G & Gamma ~=~ G' ->
    G' |= Gamma' |- unbox_fetch_LF M ::: A

| t_here_LF: forall A G Gamma M
  (Ok: ok_Bg (Gamma :: G))
  (H: G |= Gamma |- M ::: A),
  G |= Gamma |- here_LF M ::: <*> A

| t_get_here_LF: forall A G Gamma Gamma' M
  (Ok: ok_Bg (Gamma :: G & Gamma'))
  (H: G & Gamma' |= Gamma |- M ::: A),
  forall G', G & Gamma ~=~ G' ->
    G' |= Gamma' |- get_here_LF M ::: <*> A

| t_letdia_LF: forall L A B G Gamma M N
  (Ok_Bg: ok_Bg (Gamma :: G))
  (HT1: G |= Gamma |- M ::: <*> A)
  (HT2: forall v, v \notin L ->
    ((v, A) :: nil) :: G |= Gamma |- N ^^ (hyp_LF (fte v)) ::: B),
  G |= Gamma |- letdia_LF M N ::: B

| t_letdia_get_LF: forall L A B G Gamma Gamma' M N
  (Ok_Bg: ok_Bg (Gamma :: G & Gamma'))
  (HT1: G & Gamma' |= Gamma |- M ::: <*> A)
  (HT2: forall v, v \notin L ->
    ((v, A) :: nil) :: G & Gamma |= Gamma' |- N ^^ (hyp_LF (fte v)) ::: B),
  forall G0, G & Gamma ~=~ G0 ->
    G0 |= Gamma' |- letdia_get_LF M N ::: B

where " G '|=' Gamma '|-' M ':::' A" := (types_LF G Gamma M A).

Inductive value_LF: te_LF -> Prop :=
| val_lam: forall A M, value_LF (lam_LF A M)
| val_box: forall M, value_LF (box_LF M)
| val_here: forall M, value_LF M -> value_LF (here_LF M)
| val_get_here: forall M, value_LF M -> value_LF (get_here_LF M)
.

Reserved Notation " M |-> N " (at level 70).

Inductive step_LF: te_LF -> te_LF -> Prop :=

| red_appl_lam_LF: forall M N A,
  lc_n_LF 1 M -> lc_LF N ->
  appl_LF (lam_LF A M) N |-> [N // bte 0] M

| red_unbox_box_LF: forall M,
  lc_LF M ->
  unbox_LF (box_LF M) |-> M

| red_unbox_fetch_box_LF: forall M,
  lc_LF M ->
  unbox_fetch_LF (box_LF M) |-> M

| red_letdia_here_LF: forall M N,
  lc_LF M -> lc_n_LF 1 N ->
  letdia_LF (here_LF M) N |-> N ^^ M

| red_letdia__get_here_LF: forall M N,
  lc_LF M -> lc_n_LF 1 N ->
  letdia_LF (get_here_LF M) N |-> N ^^ M

| red_letdia_get__here_LF: forall M N,
  lc_LF M -> lc_n_LF 1 N ->
  letdia_get_LF (here_LF M) N |-> N ^^ M

| red_letdia_get_get_here_LF: forall M N,
  lc_LF M -> lc_n_LF 1 N ->
  letdia_get_LF (get_here_LF M) N |-> N ^^ M

| red_appl_LF: forall M M' N,
  lc_LF M -> lc_LF N ->
  M |-> M' ->
  appl_LF M N |-> appl_LF M' N

| red_unbox_LF: forall M M',
  lc_LF M -> M |-> M' ->
  unbox_LF M |-> unbox_LF M'

| red_unbox_fetch_LF: forall M M',
  lc_LF M -> M |-> M' ->
  unbox_fetch_LF M |-> unbox_fetch_LF M'

| red_here_LF: forall M M',
  lc_LF M -> M |-> M' ->
  here_LF M |-> here_LF M'

| red_get_here_LF: forall M M',
  lc_LF M -> M |-> M' ->
  get_here_LF M |-> get_here_LF M'

| red_letdia_LF: forall M M' N,
  lc_LF M -> lc_n_LF 1 N ->
  M |-> M' ->
  letdia_LF M N |-> letdia_LF M' N

| red_letdia_get_LF:forall M M' N,
  lc_LF M -> lc_n_LF 1 N ->
  M |-> M' ->
  letdia_get_LF M N |-> letdia_get_LF M' N

where " M |-> N " := (step_LF M N ).

Inductive steps_LF : te_LF -> te_LF -> Prop :=
| single_step_LF: forall M M', M |-> M' -> steps_LF M M'
| multi_step_LF: forall M M' M'',
  M |-> M' -> steps_LF M' M'' -> steps_LF M M''
.


Lemma PPermutationG:
forall G Gamma M A G',
  G |= Gamma |- M ::: A ->
  G ~=~ G' ->
  G' |= Gamma |- M ::: A.
Admitted.

Lemma PermutationGamma:
forall G Gamma M A Gamma',
  G |= Gamma |- M ::: A ->
  Gamma *=* Gamma' ->
  G |= Gamma' |- M ::: A.
Admitted.

Lemma WeakeningG:
forall G Gamma M A Delta,
  G |= Gamma |- M ::: A ->
  ok_Bg (Gamma::Delta::G) ->
  Delta :: G |= Gamma |- M ::: A.
Admitted.

Lemma WekaneningGamma:
forall G Gamma M A Gamma',
  G |= Gamma |- M ::: A ->
  ok_Bg ((Gamma++Gamma')::G) ->
  G |= Gamma ++ Gamma' |- M ::: A.
Admitted.

Lemma WeakeningWithinG:
forall G Gamma M A Delta Delta',
  Delta::G |= Gamma |- M ::: A ->
  ok_Bg (Gamma:: (Delta ++ Delta') :: G) ->
  (Delta++Delta') :: G |= Gamma |- M ::: A.
Admitted.

Fixpoint emptyEquiv (G: list (list (var * ty))) :=
match G with
| nil => nil
| a::G' => (@nil (var * ty)) :: emptyEquiv G'
end.

Lemma Progress:
forall G M A
  (H_lc_t: lc_LF M)
  (HT: emptyEquiv G |= nil |- M ::: A),
  value_LF M \/ exists N, M |-> N.
Admitted.

Lemma Preservation:
forall G M N A
  (HT: emptyEquiv G |= nil |- M ::: A)
  (HS: M |-> N),
  emptyEquiv G |= nil |- N ::: A.
Admitted.