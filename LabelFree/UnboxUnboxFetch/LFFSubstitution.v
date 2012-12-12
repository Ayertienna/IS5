Require Import PermutLib.
Require Import LFFSyntax.
Require Import Arith.

Open Scope permut_scope.

Reserved Notation " [ M // x ] N " (at level 5).

Fixpoint subst_t_LF M x N :=
match N with
| hyp_LF v => if (eq_vte_dec x v) then M else N
| lam_LF t N' => lam_LF t [M//shift_vte x]N'
| appl_LF N' N'' => appl_LF [M//x]N' [M//x]N''
| box_LF N' => box_LF [M//x]N'
| unbox_LF N' => unbox_LF [M//x]N'
| unbox_fetch_LF C N' => unbox_fetch_LF C [M//x]N'
| here_LF N' => here_LF [M//x]N'
| get_here_LF C N' => get_here_LF C [M//x]N'
| letdia_LF N' N'' => letdia_LF [M//x]N' [M//shift_vte x]N''
| letdia_get_LF C N' N'' => letdia_get_LF C [M//x]N' [M//shift_vte x]N''
end
where " [ M // x ] N " := (subst_t_LF M x N).

Definition open_LF (M: te_LF) (t: te_LF) := subst_t_LF t (bte 0) M.
Notation " M '^t^' t " := (open_LF M t) (at level 67).

Inductive equiv_vctx: vctx -> vctx -> Prop :=
| equiv_same: forall n, equiv_vctx (bctx n) (bctx n)
| equiv_permut: forall l l',
  l *=* l' -> equiv_vctx (cctx l) (cctx l').

Notation " C1 ~~  C2 " := (equiv_vctx C1 C2) (at level 67).

Lemma eq_vctx_dec:
forall (v1: vctx) v2,
  {v1 ~~ v2} + {v1 ~~ v2}.
Admitted.

Inductive merge_outer_LF : ctx_LF -> ctx_LF -> list var -> te_LF ->
  te_LF -> Prop :=

| merge_hyp_outer_LF:
  forall U Gamma Delta v,
    merge_outer_LF Gamma Delta U (hyp_LF v) (hyp_LF v)

| merge_lam_outer_LF:
  forall U Gamma Delta M M' A,
    (forall v, v \notin (from_list U) ->
      merge_outer_LF ((v,A)::Gamma) Delta (v::U) M M') ->
    merge_outer_LF Gamma Delta U (lam_LF A M) (lam_LF A M')

| merge_appl_outer_LF:
  forall U Gamma Delta M M' N N',
    merge_outer_LF Gamma Delta U M M' ->
    merge_outer_LF Gamma Delta U N N' ->
    merge_outer_LF Gamma Delta U (appl_LF M N) (appl_LF M' N')

| merge_box_outer_LF:
  forall U Gamma Delta M M',
    merge_outer_LF Gamma Delta U M M' ->
    merge_outer_LF Gamma Delta U (box_LF M) (box_LF M')

with merge_new_LF: ctx_LF -> ctx_LF -> list var -> te_LF -> te_LF -> Prop
:=
| merge_new_hyp: forall Gamma Delta U v,
  merge_new_LF Gamma Delta U (hyp_LF v) (hyp_LF v)
| merge_new_lam:
  forall U Gamma Delta A M M',
    (forall v, v \notin (from_list U) ->
      merge_new_LF ((v,A)::Gamma) Delta (v::U) M M') ->
    merge_new_LF Gamma Delta U (lam_LF A M) (lam_LF A M')
| merge_new_appl:
  forall U Gamma Delta M N M' N',
    merge_new_LF Gamma Delta U M M' ->
    merge_new_LF Gamma Delta U N N' ->
    merge_new_LF Gamma Delta U (appl_LF M N) (appl_LF M' N')

| merge_box_new_LF:
  forall U Gamma Delta M M',
    merge_outer_LF Gamma Delta U M M' ->
    merge_new_LF Gamma Delta U (box_LF M) (box_LF M')
.







(*
Inductive merge_outer_LF : ctx_LF -> ctx_LF -> te_LF -> te_LF -> Prop :=

| merge_hyp_outer_LF:
  forall Gamma Delta v,
    merge_outer_LF Gamma Delta (hyp_LF v) (hyp_LF v)

| merge_lam_outer_LF:
  forall Gamma Delta M M' A,
    merge_outer_LF Gamma Delta M M' ->
    merge_outer_LF Gamma Delta (lam_LF A M) (lam_LF A M')

| merge_appl_outer_LF:
  forall Gamma Delta M M' N N',
    merge_outer_LF Gamma Delta M M' ->
    merge_outer_LF Gamma Delta N N' ->
    merge_outer_LF Gamma Delta (appl_LF M N) (appl_LF M' N')

| merge_box_outer_LF:
  forall Gamma Delta M M',
    merge_outer_LF Gamma Delta M M' ->
    merge_outer_LF Gamma Delta (box_LF M) (box_LF M')

| merge_unbox_outer_LF:
  forall Gamma Delta M M',
    merge_outer_LF Gamma Delta M M' ->
    merge_outer_LF Gamma Delta (unbox_LF M) (unbox_LF M')

| merge_unbox_fetch_new_outer_LF:
  forall Gamma Delta Iota M M',
    merge_new_LF Gamma Delta M M' ->
    cctx Gamma ~~ Iota ->
    merge_outer_LF Gamma Delta (unbox_fetch_LF Iota M)
                               (unbox_fetch_LF (cctx (Gamma++Delta)) M')
| merge_unbox_fetch_old_outer_LF:
  forall Gamma Delta Iota M M',
    merge_old_LF Gamma Delta M M' ->
    cctx Delta ~~ Iota ->
    merge_outer_LF Gamma Delta (unbox_fetch_LF Iota M)
                               (unbox_fetch_LF (cctx (Gamma++Delta)) M')
| merge_unbox_fetch_outer_outer_LF:
  forall Gamma Delta Iota M M',
    merge_outer_LF Gamma Delta M M' ->
    ~ (cctx Gamma ~~ Iota) -> ~ (cctx Delta ~~ Iota) ->
    merge_outer_LF Gamma Delta (unbox_fetch_LF Iota M) (unbox_fetch_LF Iota M')

| merge_here_outer_LF:
  forall Gamma Delta M M',
    merge_outer_LF Gamma Delta M M' ->
    merge_outer_LF Gamma Delta (here_LF M) (here_LF M')

| merge_get_here_new_outer_LF:
  forall Gamma Delta Iota M M',
    merge_new_LF Gamma Delta M M' ->
    cctx Gamma ~~ Iota ->
    merge_outer_LF Gamma Delta (get_here_LF Iota M)
                               (get_here_LF (cctx (Gamma++Delta)) M')
| merge_get_here_old_outer_LF:
  forall Gamma Delta Iota M M',
    merge_old_LF Gamma Delta M M' ->
    cctx Delta ~~ Iota ->
    merge_outer_LF Gamma Delta (get_here_LF Iota M)
                               (get_here_LF (cctx (Gamma++Delta)) M')
| merge_get_here_outer_outer_LF:
  forall Gamma Delta Iota M M',
    merge_outer_LF Gamma Delta M M' ->
    ~ (cctx Gamma ~~ Iota) -> ~ (cctx Delta ~~ Iota) ->
    merge_outer_LF Gamma Delta (get_here_LF Iota M) (get_here_LF Iota M')

| merge_letdia_outer_LF:
  forall Gamma Delta M N M' N',
    merge_outer_LF Gamma Delta M M' ->
    merge_outer_LF Gamma Delta N N' ->
    merge_outer_LF Gamma Delta (letdia_LF M N) (letdia_LF M' N')

| merge_letdia_get_new_outer_LF:
  forall Gamma Delta Iota M N M' N',
    merge_new_LF Gamma Delta M M' ->
    merge_outer_LF Gamma Delta N N' ->
    cctx Gamma ~~ Iota ->
    merge_outer_LF Gamma Delta (letdia_get_LF Iota M N)
                               (letdia_get_LF (cctx (Gamma++Delta)) M' N')
| merge_letdia_get_old_outer_LF:
  forall Gamma Delta Iota M N M' N',
    merge_old_LF Gamma Delta M M' ->
    merge_outer_LF Gamma Delta N N' ->
    cctx Delta ~~ Iota ->
    merge_outer_LF Gamma Delta (letdia_get_LF Iota M N)
                               (letdia_get_LF (cctx (Gamma++Delta)) M' N')
| merge_letdia_get_outer_outer_LF:
  forall Gamma Delta Iota M N M' N',
    merge_outer_LF Gamma Delta M M' ->
    merge_outer_LF Gamma Delta N N' ->
    ~ (cctx Gamma ~~ Iota) -> ~ (cctx Delta ~~ Iota) ->
    merge_outer_LF Gamma Delta (letdia_get_LF Iota M N)
                               (letdia_get_LF Iota M' N')

with merge_new_LF : ctx_LF -> ctx_LF -> te_LF -> te_LF -> Prop :=

| merge_hyp_new_LF:
  forall Gamma Delta v,
    merge_new_LF Gamma Delta (hyp_LF v) (hyp_LF v)

| merge_lam_new_LF:
  forall Gamma Delta M M' A v,
    merge_new_LF ((v, A)::Gamma) Delta M M' ->
    merge_new_LF Gamma Delta (lam_LF A M) (lam_LF A M')

| merge_appl_new_LF:
  forall Gamma Delta M M' N N',
    merge_new_LF Gamma Delta M M' ->
    merge_new_LF Gamma Delta N N' ->
    merge_new_LF Gamma Delta (appl_LF M N) (appl_LF M' N')

| merge_box_new_LF:
  forall Gamma Delta M M',
    merge_outer_LF Gamma Delta M M' ->
    merge_new_LF Gamma Delta (box_LF M) (box_LF M')

| merge_unbox_new_LF:
  forall Gamma Delta M M',
    merge_new_LF Gamma Delta M M' ->
    merge_new_LF Gamma Delta (unbox_LF M) (unbox_LF M')

| merge_unbox_fetch_old_new_LF:
  forall Gamma Delta Iota M M',
    merge_old_LF Gamma Delta M M' ->
    cctx Delta ~~ Iota ->
    merge_new_LF Gamma Delta (unbox_fetch_LF Iota M)
                             (unbox_LF M')
| merge_unbox_fetch_outer_new_LF:
  forall Gamma Delta Iota M M',
    merge_outer_LF Gamma Delta M M' ->
    ~ (cctx Delta ~~ Iota) ->
    merge_new_LF Gamma Delta (unbox_fetch_LF Iota M) (unbox_fetch_LF Iota M')

| merge_here_new_LF:
  forall Gamma Delta M M',
    merge_new_LF Gamma Delta M M' ->
    merge_new_LF Gamma Delta (here_LF M) (here_LF M')

| merge_get_here_old_new_LF:
  forall Gamma Delta Iota M M',
    merge_old_LF Gamma Delta M M' ->
    cctx Delta ~~ Iota ->
    merge_new_LF Gamma Delta (get_here_LF Iota M)
                             (here_LF M')
| merge_get_here_outer_new_LF:
  forall Gamma Delta Iota M M',
    merge_outer_LF Gamma Delta M M' ->
    ~ (cctx Delta ~~ Iota) ->
    merge_new_LF Gamma Delta (get_here_LF Iota M) (get_here_LF Iota M')

| merge_letdia_new_LF:
  forall Gamma Delta M N M' N',
    merge_new_LF Gamma Delta M M' ->
    merge_new_LF Gamma Delta N N' ->
    merge_new_LF Gamma Delta (letdia_LF M N) (letdia_LF M' N')

| merge_letdia_get_old_new_LF:
  forall Gamma Delta Iota M N M' N',
    merge_old_LF Gamma Delta M M' ->
    merge_new_LF Gamma Delta N N' ->
    cctx Delta ~~ Iota ->
    merge_new_LF Gamma Delta (letdia_get_LF Iota M N)
                              (letdia_LF M' N')
| merge_letdia_get_outer_new_LF:
  forall Gamma Delta Iota M N M' N',
    merge_outer_LF Gamma Delta M M' ->
    merge_new_LF Gamma Delta N N' ->
    ~ (cctx Delta ~~ Iota) ->
    merge_new_LF Gamma Delta (letdia_get_LF Iota M N)
                             (letdia_get_LF Iota M' N')

with merge_old_LF : ctx_LF -> ctx_LF -> te_LF -> te_LF -> Prop :=

| merge_hyp_old_LF:
  forall Gamma Delta v,
    merge_old_LF Gamma Delta (hyp_LF v) (hyp_LF v)

| merge_lam_old_LF:
  forall Gamma Delta M M' A v,
    merge_old_LF Gamma ((v,A)::Delta) M M' ->
    merge_old_LF Gamma Delta (lam_LF A M) (lam_LF A M')

| merge_appl_old_LF:
  forall Gamma Delta M M' N N',
    merge_old_LF Gamma Delta M M' ->
    merge_old_LF Gamma Delta N N' ->
    merge_old_LF Gamma Delta (appl_LF M N) (appl_LF M' N')

| merge_box_old_LF:
  forall Gamma Delta M M',
    merge_outer_LF Gamma Delta M M' ->
    merge_old_LF Gamma Delta (box_LF M) (box_LF M')

| merge_unbox_old_LF:
  forall Gamma Delta M M',
    merge_old_LF Gamma Delta M M' ->
    merge_old_LF Gamma Delta (unbox_LF M) (unbox_LF M')

| merge_unbox_fetch_new_old_LF:
  forall Gamma Delta Iota M M',
    merge_new_LF Gamma Delta M M' ->
    cctx Gamma ~~ Iota ->
    merge_old_LF Gamma Delta (unbox_fetch_LF Iota M)
                             (unbox_LF M')
| merge_unbox_fetch_outer_old_LF:
  forall Gamma Delta Iota M M',
    merge_outer_LF Gamma Delta M M' ->
    ~ (cctx Gamma ~~ Iota) ->
    merge_old_LF Gamma Delta (unbox_fetch_LF Iota M) (unbox_fetch_LF Iota M')

| merge_here_old_LF:
  forall Gamma Delta M M',
    merge_old_LF Gamma Delta M M' ->
    merge_old_LF Gamma Delta (here_LF M) (here_LF M')

| merge_get_here_new_old_LF:
  forall Gamma Delta Iota M M',
    merge_new_LF Gamma Delta M M' ->
    cctx Gamma ~~ Iota ->
    merge_old_LF Gamma Delta (get_here_LF Iota M)
                             (here_LF M')
| merge_get_here_outer_old_LF:
  forall Gamma Delta Iota M M',
    merge_outer_LF Gamma Delta M M' ->
    ~ (cctx Gamma ~~ Iota) ->
    merge_old_LF Gamma Delta (get_here_LF Iota M) (get_here_LF Iota M')

| merge_letdia_old_LF:
  forall Gamma Delta M N M' N',
    merge_old_LF Gamma Delta M M' ->
    merge_old_LF Gamma Delta N N' ->
    merge_old_LF Gamma Delta (letdia_LF M N) (letdia_LF M' N')

| merge_letdia_get_new_old_LF:
  forall Gamma Delta Iota M N M' N',
    merge_new_LF Gamma Delta M M' ->
    merge_old_LF Gamma Delta N N' ->
    cctx Gamma ~~ Iota ->
    merge_old_LF Gamma Delta (letdia_get_LF Iota M N)
                              (letdia_LF M' N')
| merge_letdia_get_outer_old_LF:
  forall Gamma Delta Iota M N M' N',
    merge_outer_LF Gamma Delta M M' ->
    merge_old_LF Gamma Delta N N' ->
    ~ (cctx Gamma ~~ Iota) ->
    merge_old_LF Gamma Delta (letdia_get_LF Iota M N)
                             (letdia_get_LF Iota M' N')

.

Reserved Notation " {{ C // x | G }} N " (at level 5).
Reserved Notation " {{ C // x | | G }} N " (at level 5).

Fixpoint open_c_outer_LF (M0: te_LF) (n: nat) (C: vctx) (G: ctx_LF) :=
match M0 with
| hyp_LF v => hyp_LF v
| lam_LF A M => lam_LF A {{C//n}}M
| appl_LF M N => appl_LF {{C//n}}M {{C//n}}N
| box_LF M => box_LF {{C//S n}}M
| unbox_LF M => unbox_LF {{C//n}}M
| here_LF M => here_LF {{C//n}}M
| letdia_LF M N => letdia_LF {{C//n}}M {{C//n}}N
| unbox_fetch_LF (bctx m) M =>
  let C' := if (eq_nat_dec m n) then C else bctx m in
  unbox_fetch_LF C' {{C//n}}M
| unbox_fetch_LF (cctx C') M =>
  unbox_fetch_LF (cctx C') {{C//n}}M
| get_here_LF (bctx m) M =>
  let C' := if (eq_nat_dec m n) then C else bctx m in
  get_here_LF C' {{C//n}}M
| get_here_LF (cctx C') M =>
  get_here_LF (cctx C') {{C//n}}M
| letdia_get_LF (bctx m) M N =>
  let C' := if (eq_nat_dec m n) then C else bctx m in
  letdia_get_LF C' {{C//n}}M {{C//S n}}N
| letdia_get_LF (cctx C') M N =>
  letdia_get_LF (cctx C') {{C//n}}M {{C//S n}}N
end
with open_c_inner_LF (M0: te_LF) (n: nat) (C: vctx) (G: ctx_LF) :=
where " {{ C // n | G }} M " := (open_c_LF M n C G).
*)