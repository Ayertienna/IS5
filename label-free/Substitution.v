Require Export Syntax.
Require Import Metatheory.
Require Import Arith.
Require Import List.

Open Scope label_free_is5_scope.

Definition var_from (w: ctx_LF):=
match w with
| fctx w0 => \{w0}
| bctx _ => \{}
end.

(* Term substitution *)

(* We want to substitute M for nth hyp. in term N0 when the context is ctx.
   We also know, that current context isn't ctx. *)
Fixpoint subst_t_outer (M0: te_LF) (n: nat) (ctx: ctx_LF) (N0: te_LF) :=
match N0 with
| hyp_LF n => 
    hyp_LF n
| lam_LF A M => 
    lam_LF A (subst_t_outer M0 n ctx M)
| appl_LF M N => 
    appl_LF (subst_t_outer M0 n ctx M) (subst_t_outer M0 n ctx N)
| box_LF M => 
    box_LF (subst_t_outer M0 n ctx M)
| unbox_fetch_LF w M => 
  let M' := If (ctx = w) then subst_t_inner M0 n M ctx
            else subst_t_outer M0 n ctx M in
    unbox_fetch_LF w M'
| get_here_LF w M =>
  let M' := If (ctx = w) then subst_t_inner M0 n M ctx
            else subst_t_outer M0 n ctx M in
    get_here_LF w M'        
| letdia_get_LF w M N =>
  let M' := If (ctx = w) then subst_t_inner M0 n M ctx
            else subst_t_outer M0 n ctx M in
  let N' := subst_t_outer M0 n ctx N in
    letdia_get_LF w M' N'
end
(* Current context is exactly the context in which we want to do susbtitution *)
with subst_t_inner (M0: te_LF) (n: nat) (N0: te_LF) (curr: ctx_LF) {struct N0} :=
match N0 with
| hyp_LF m => 
    if (eq_nat_dec m n) then M0 else hyp_LF m
| lam_LF A M => 
    lam_LF A (subst_t_inner M0 (S n) M curr)
| appl_LF M N => 
    appl_LF (subst_t_inner M0 n M curr) (subst_t_inner M0 n N curr)
| box_LF M =>
    box_LF (subst_t_outer M0 n curr M)
| unbox_fetch_LF w M =>
  let M' := If (curr = w) then subst_t_inner M0 n M curr
            else subst_t_outer M0 n curr M in
    unbox_fetch_LF w M'
| get_here_LF w M =>
  let M' := If (curr = w) then subst_t_inner M0 n M curr
            else subst_t_outer M0 n curr M in
    get_here_LF w M'
| letdia_get_LF w M N =>
  let M' := If (curr = w) then subst_t_inner M0 n M curr
            else subst_t_outer M0 n curr M in
  let N' := subst_t_inner M0 n N curr in
    letdia_get_LF w M' N'
end.

Definition subst_t M n ctx N curr :=
  If ctx = curr then (subst_t_inner M n N ctx) 
  else (subst_t_outer M n ctx N). 

Notation " [ M // n | ctx ] [ N | curr ] " := 
  (subst_t M n ctx N curr) (at level 5) : label_free_is5_scope.

Fixpoint subst_list L n N subst_ctx curr_ctx :=
match L with
| nil => N
| M :: L' => [M//n | subst_ctx] 
             [subst_list L' (S n) N subst_ctx curr_ctx | curr_ctx]
end.

(* Context substitution *)

Definition recalc_simpl_ctx (ctx:ctx_LF) : ctx_LF :=
  match ctx with
    | fctx _ => ctx
    | bctx n => bctx (S n)
end.

Definition recalculate_ctx (ctx1: ctx_LF) (ctx2: ctx_LF) : prod ctx_LF ctx_LF :=
  (recalc_simpl_ctx ctx1, recalc_simpl_ctx ctx2).

(* We want to substitute ctx1 for every occ. of ctx2; our current context is
   curr. *)
(* In subst_ctx_outer it is assumed that current context is neither ctx1
   nor ctx2 *)
Fixpoint subst_ctx_outer (M0 : te_LF) (ctx1: ctx_LF) (ctx2: ctx_LF)
                         (len_old: nat) :=
match M0 with 
| hyp_LF n => hyp_LF n

| lam_LF A M => lam_LF A (subst_ctx_outer M ctx1 ctx2 len_old)

| appl_LF M N => appl_LF (subst_ctx_outer M ctx1 ctx2 len_old) 
                         (subst_ctx_outer N ctx1 ctx2 len_old)

| box_LF M => 
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
    box_LF (subst_ctx_outer M ctx1' ctx2' len_old)

| unbox_fetch_LF w M => 
  let M' := If (w = ctx1) then subst_ctx_new M ctx1 ctx2 len_old
            else If (w = ctx2) then subst_ctx_old M ctx1 ctx2 len_old
            else subst_ctx_outer M ctx1 ctx2 len_old in
  unbox_fetch_LF w M'

| get_here_LF w M =>
  let M' := If (w = ctx1) then subst_ctx_new M ctx1 ctx2 len_old
            else If (w = ctx2) then subst_ctx_old M ctx1 ctx2 len_old
            else subst_ctx_outer M ctx1 ctx2 len_old in
  get_here_LF w M'

| letdia_get_LF w M N =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in
  let M' := If (w = ctx1) then subst_ctx_new M ctx1 ctx2 len_old
            else If (w = ctx2) then subst_ctx_old M ctx1 ctx2 len_old
            else subst_ctx_outer M ctx1 ctx2 len_old in
  let N' := subst_ctx_outer N ctx1' ctx2' len_old in
  letdia_get_LF w M' N'
end

(* In subst_ctx_old we assume that current context was ctx2 *)
with subst_ctx_old (M0 : te_LF) (ctx1: ctx_LF) (ctx2: ctx_LF) (len_old: nat) :=
match M0 with 
| hyp_LF n => hyp_LF n

| lam_LF A M => lam_LF A (subst_ctx_old M ctx1 ctx2 (len_old))

| appl_LF M N => appl_LF (subst_ctx_old M ctx1 ctx2 len_old) 
                         (subst_ctx_old N ctx1 ctx2 len_old)

| box_LF M =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in     
    box_LF (subst_ctx_outer M ctx1' ctx2' len_old)

| unbox_fetch_LF w M =>
  let M' := If (w = ctx1) then subst_ctx_new M ctx1 ctx2 len_old
            else If (w = ctx2) then subst_ctx_old M ctx1 ctx2 len_old
            else subst_ctx_outer M ctx1 ctx2 len_old in
  unbox_fetch_LF w M'

| get_here_LF w M =>
  let M' := If (w = ctx1) then subst_ctx_new M ctx1 ctx2 len_old
            else If (w = ctx2) then subst_ctx_old M ctx1 ctx2 len_old
            else subst_ctx_outer M ctx1 ctx2 len_old in
  get_here_LF w M'

| letdia_get_LF w M N =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in
  let M' := If (w = ctx1) then subst_ctx_new M ctx1 ctx2 len_old
            else If (w = ctx2) then subst_ctx_old M ctx1 ctx2 len_old
            else subst_ctx_outer M ctx1 ctx2 len_old in
  let N' := subst_ctx_old N ctx1' ctx2' len_old in
  letdia_get_LF w M' N'
end

(* In subst_ctx_new we assume that current context is ctx1 *)
with subst_ctx_new (M0 : te_LF) (ctx1: ctx_LF) (ctx2: ctx_LF) (len_old: nat) :=
match M0 with 

(* It is assumed that when ctx2 = bctx _, then len_old is 0 *)
| hyp_LF n => hyp_LF (len_old + n)

| lam_LF A M => lam_LF A (subst_ctx_new M ctx1 ctx2 len_old)

| appl_LF M N => appl_LF (subst_ctx_new M ctx1 ctx2 len_old) 
                         (subst_ctx_new N ctx1 ctx2 len_old)

| box_LF M =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
    box_LF (subst_ctx_outer M ctx1' ctx2' len_old)

| unbox_fetch_LF w M =>
  let M' := If (w = ctx1) then subst_ctx_new M ctx1 ctx2 len_old
            else If (w = ctx2) then subst_ctx_old M ctx1 ctx2 len_old
            else subst_ctx_outer M ctx1 ctx2 len_old in
  unbox_fetch_LF w M'

| get_here_LF w M =>
  let M' := If (w = ctx1) then subst_ctx_new M ctx1 ctx2 len_old
            else If (w = ctx2) then subst_ctx_old M ctx1 ctx2 len_old
            else subst_ctx_outer M ctx1 ctx2 len_old in
  get_here_LF w M'

| letdia_get_LF w M N =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in
  let M' := If (w = ctx1) then subst_ctx_new M ctx1 ctx2 len_old
            else If (w = ctx2) then subst_ctx_old M ctx1 ctx2 len_old
            else subst_ctx_outer M ctx1 ctx2 len_old in
  let N' := subst_ctx_old N ctx1' ctx2' len_old in
  letdia_get_LF w M' N'
end.

Definition subst_ctx M c1 c2 curr len_old :=
If c1 = c2 then M
else
  If curr = c1 then
    subst_ctx_new M c1 c2 len_old
  else
    If curr = c2 then
      subst_ctx_old M c1 c2 len_old
    else
      subst_ctx_outer M c1 c2 len_old.

Notation " {{ c1 // c2 }} [ M | curr , m ] " := 
  (subst_ctx M c1 c2 curr m) (at level 5) : label_free_is5_scope.

Definition open_ctx M ctx curr := subst_ctx M ctx (bctx 0) curr 0.

Notation " M ^^ [ w | w' ] " := (open_ctx M w w') (at level 10) : label_free_is5_scope.


Section Lemmas.

Lemma subst_t__inner:
forall M k N w,
  subst_t_inner M k N w = [M//k | w] [N | w].
intros;
unfold subst_t;
case_if;
reflexivity.
Qed.

Lemma subst_t__outer:
forall M k N w w'
  (Neq: w <> w'),
  subst_t_outer M k w N = [M//k | w] [N | w'].
intros; unfold subst_t;
case_if; reflexivity.
Qed.

Lemma subst_ctx__old:
forall M c1 c2 len_old
  (Neq: c1 <> c2),
  subst_ctx_old M c1 c2 len_old = {{ c1 // c2 }} [M | c2, len_old].
intros;
unfold subst_ctx;
repeat case_if;
reflexivity.
Qed.

Lemma subst_ctx__new:
forall M c1 c2 len_old
  (Neq: c1 <> c2),
  subst_ctx_new M c1 c2 len_old = {{ c1 // c2 }} [M | c1, len_old].
intros;
unfold subst_ctx;
repeat case_if;
reflexivity.
Qed.

Lemma subst_ctx__outer:
forall M c1 c2 curr len_old
  (Neq: c1 <> c2)
  (Neq': c1 <> curr)
  (Neq'': c2 <> curr),
  subst_ctx_outer M c1 c2 len_old = {{ c1 // c2 }} [M | curr, len_old].
intros;
unfold subst_ctx;
repeat case_if;
reflexivity.
Qed.

Ltac try_rewrite_subst :=
try repeat rewrite subst_t__inner;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__old.

Lemma no_unbound_worlds_LF_subst_w_id:
forall M n
  (H_unbound: unbound_worlds n M = nil),
  forall w w0, {{ w // bctx n }} [M | w0, 0] = M.
induction M; intros; unfold subst_ctx.
(* hyp *)
repeat case_if; reflexivity.
(* lam *)
unfold subst_ctx in *;
simpl in H_unbound;
specialize IHM with n w w0;
apply IHM with (w:=w) (w0:=w0) in H_unbound;
repeat case_if; simpl; 
try rewrite H_unbound; 
auto.
(* appl *)
unfold subst_ctx in *;
simpl in H_unbound;
apply app_eq_nil in H_unbound;
destruct H_unbound as (H_Un1, H_Un2);
apply IHM1 with (w:=w) (w0:=w0) in H_Un1;
apply IHM2 with (w:=w) (w0:=w0) in H_Un2;
repeat case_if; simpl;
try (rewrite H_Un1; rewrite H_Un2); reflexivity.
(* box *)
inversion H_unbound; subst;
apply IHM with (w:=w) (w0:=w0) in H0;
repeat case_if; simpl; try subst; auto;
unfold recalc_simpl_ctx;
assert (exists w0, w0 \notin free_worlds_LF M \u var_from w) by
  (exists (var_gen (free_worlds_LF M \u var_from w)); apply var_gen_spec).
destruct H2 as (w_fresh);
rewrite notin_union in H2; destruct H2;
rewrite subst_ctx__outer with (curr := fctx w_fresh);
try rewrite IHM; eauto; try discriminate;
destruct w; simpl in H3;
try (intro nn; inversion nn; subst n0; elim H; reflexivity);
try discriminate;
rewrite notin_singleton in H3;
intro nn; inversion nn; subst v; elim H3; reflexivity.

destruct H3 as (w_fresh);
rewrite notin_union in H3; destruct H3;
rewrite subst_ctx__outer with (curr := fctx w_fresh);
try rewrite IHM; eauto; try discriminate;
destruct w; simpl in H4;
try (intro nn; inversion nn; subst n0; elim H; reflexivity);
try discriminate;
rewrite notin_singleton in H4;
intro nn; inversion nn; subst v; elim H4; reflexivity.

destruct H3 as (w_fresh);
rewrite notin_union in H3; destruct H3;
rewrite subst_ctx__outer with (curr := fctx w_fresh);
try rewrite IHM; eauto; try discriminate;
destruct w; simpl in H4;
try (intro nn; inversion nn; subst n0; elim H; reflexivity);
try discriminate;
rewrite notin_singleton in H4;
intro nn; inversion nn; subst v; elim H4; reflexivity.
(* unbox_fetch *)
inversion H_unbound; destruct c; simpl; try discriminate;
assert (exists w0, w0 \notin free_worlds_LF M \u var_from w) by
  (exists (var_gen (free_worlds_LF M \u var_from w)); apply var_gen_spec);
destruct H as (w_fresh);
repeat case_if; simpl;
try rewrite subst_ctx__old;
try rewrite subst_ctx__new;
try rewrite subst_ctx__outer with (curr:=fctx w_fresh);
try discriminate;
try rewrite IHM; 
eauto;
rewrite notin_union in H; unfold var_from in *;
destruct w;
try rewrite notin_singleton in H;
destruct H; try discriminate;
intro nn; inversion nn; subst w_fresh. 
elim H5; reflexivity.
elim H6; reflexivity.
elim H6; reflexivity.
(* get_here *)
inversion H_unbound; destruct c; simpl; try discriminate;
assert (exists w0, w0 \notin free_worlds_LF M \u var_from w) by
  (exists (var_gen (free_worlds_LF M \u var_from w)); apply var_gen_spec);
destruct H as (w_fresh);
rewrite notin_union in H; unfold var_from in *;
destruct w;
try rewrite notin_singleton in H; destruct H;
repeat case_if; simpl;
try rewrite subst_ctx__old;
try rewrite subst_ctx__new;
try rewrite subst_ctx__outer with (curr := fctx w_fresh);
try discriminate;
try rewrite IHM; 
eauto;
intro nn; inversion nn; subst w_fresh;
elim H1; reflexivity.

(* letdia_get *)
inversion H_unbound; destruct c; simpl; try discriminate;
apply app_eq_nil in H0; destruct H0;
assert (exists w0, w0 \notin free_worlds_LF M1 \u free_worlds_LF M2 \u var_from w) by
  (exists (var_gen (free_worlds_LF M1 \u free_worlds_LF M2 \u var_from w)); apply var_gen_spec);
destruct H1 as (w_fresh);
repeat rewrite notin_union in H1; unfold var_from in *;
destruct H1; destruct H2; destruct w;
repeat rewrite notin_singleton in H3; 
repeat case_if; simpl;
eauto;
unfold recalc_simpl_ctx in *;
try destruct w0;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__outer with (curr := fctx w_fresh);
try discriminate;
try rewrite IHM1;
try rewrite IHM2; 
eauto;
try inversion H5;
try (intro nn; inversion nn; subst; elim H4; reflexivity);
try (intro nn; inversion nn; subst; elim H3; reflexivity).
Qed.

Lemma closed_ctx_subst_id:
forall M w n curr
  (H_lc: lc_w_n_LF M n),
  {{w // bctx n}} [ M | curr, 0] = M.
intros;
apply no_unbound_worlds_LF_subst_w_id;
apply closed_no_unbound_worlds;
assumption.
Qed.

Lemma subst_order_irrelevant:
forall N w w' M n m w0 w1
  (HT_M: lc_w_LF M),
    [M // n | w0] [{{w1 // bctx m}}[N | w, 0] | w'] = 
    {{w1 // bctx m}}[ [M // n | w0] [N | w'] | w, 0].
induction N; unfold subst_t; unfold subst_ctx; intros;
remember (var_from w \u var_from w' \u var_from w0 \u var_from w1) as known_worlds;
assert (exists w', w' \notin known_worlds) by
  (exists (var_gen known_worlds); eapply var_gen_spec);
destruct H as (w_fresh); subst; repeat rewrite notin_union in *;
repeat rewrite notin_singleton in *;
destruct H; destruct H0; destruct H1.
(* hyp *)
repeat (case_if; simpl in * ); subst; simpl in *; try reflexivity;
try_rewrite_subst; auto;
try rewrite subst_ctx__outer with (curr := fctx w_fresh); eauto;
try rewrite closed_ctx_subst_id; auto;
try discriminate;
try (intro nn; inversion nn; subst;
     simpl in H2; rewrite notin_singleton in H2;
     elim H2; reflexivity);
unfold lc_w_LF in HT_M; replace m with (0+m) by omega;
apply closed_w_addition; assumption.
(* lam *)
repeat case_if; subst; simpl in *; eauto;
try_rewrite_subst; auto;
repeat erewrite subst_t__outer; eauto;
repeat rewrite subst_ctx__outer with (curr := fctx w_fresh); simpl;
eauto;
try rewrite IHN; eauto;
try destruct w1;
try discriminate;
try (simpl in *; rewrite notin_singleton in H2; intro nn;
     inversion nn; subst; elim H2; reflexivity).
(* appl *)
repeat (case_if; simpl in * ); subst; simpl in *;
try_rewrite_subst; simpl;
try rewrite IHN1; try rewrite IHN2; auto;
repeat erewrite subst_t__outer; eauto;
repeat rewrite subst_ctx__outer with (curr := fctx w_fresh); eauto;
try (erewrite IHN1; try erewrite IHN2; eauto);
try destruct w1;
try discriminate;
try (simpl in *; rewrite notin_singleton in *; intro nn;
  inversion nn; subst);
try elim H2; reflexivity.
(* box *)
repeat (case_if; simpl in * ); subst; simpl in *;
try_rewrite_subst; simpl;
repeat rewrite subst_t__outer with (w':= fctx w_fresh); eauto;
repeat rewrite subst_ctx__outer with (curr := fctx w_fresh); eauto;
try rewrite IHN; auto;
try destruct w0;
try destruct w1;
try destruct w;
try destruct w';
try discriminate;
try (simpl in *; rewrite notin_singleton in *; simpl; intro nn;
     inversion nn; subst);
try (elim H; reflexivity);
try (elim H0; reflexivity);
try (elim H1; reflexivity);
try (elim H2; reflexivity);
try (elim H3; reflexivity);
try (simpl; intro nn; inversion nn; subst);
try (elim H4; reflexivity). 
(* unbox_fetch *)
repeat (case_if; simpl in * ); subst; simpl in *;
try_rewrite_subst; simpl;
repeat rewrite subst_t__outer with (w':= fctx w_fresh); eauto;
repeat rewrite subst_ctx__outer with (curr := fctx w_fresh); eauto;
try rewrite IHN; auto;
try destruct w;
try destruct w';
try destruct w0;
try destruct w1;
try discriminate;
try (simpl in *; rewrite notin_singleton in *; intro nn;
  inversion nn; subst);
try (elim H; reflexivity);
try (elim H0; reflexivity);
try (elim H1; reflexivity);
try (elim H2; reflexivity);
try (elim H3; reflexivity);
try (elim H4; reflexivity);
try (elim H5; reflexivity);
try (elim H6; reflexivity).
(* get_here *)
repeat (case_if; simpl in * ); subst; simpl in *;
try_rewrite_subst; simpl;
repeat rewrite subst_t__outer with (w':= fctx w_fresh); eauto;
repeat rewrite subst_ctx__outer with (curr := fctx w_fresh); eauto;
try rewrite IHN; auto;
try destruct w;
try destruct w';
try destruct w0;
try destruct w1;
try discriminate;
try (simpl in *; rewrite notin_singleton in *; intro nn;
  inversion nn; subst);
try (elim H; reflexivity);
try (elim H0; reflexivity);
try (elim H1; reflexivity);
try (elim H2; reflexivity);
try (elim H3; reflexivity);
try (elim H4; reflexivity);
try (elim H5; reflexivity);
try (elim H6; reflexivity).
(* letdia_get *)
repeat (case_if; simpl in * ); subst; simpl in *;
try_rewrite_subst; simpl;
repeat rewrite subst_t__outer with (w':= fctx w_fresh); eauto;
repeat rewrite subst_ctx__outer with (curr := fctx w_fresh); eauto;
try rewrite IHN1;
try rewrite IHN2; auto;
try destruct w;
try destruct w';
try destruct w0;
try destruct w1;
try discriminate;
simpl;
try (simpl in *; rewrite notin_singleton in *);
try (intro nn; inversion nn; subst);
try (elim H; reflexivity);
try (elim H0; reflexivity);
try (elim H1; reflexivity);
try (elim H2; reflexivity);
try (elim H3; reflexivity);
try (elim H4; reflexivity);
try (elim H5; reflexivity);
try (elim H6; reflexivity);
try (elim H7; reflexivity);
simpl in H1; rewrite notin_singleton in H1; elim H1; reflexivity.
Qed.

End Lemmas.

Close Scope label_free_is5_scope.