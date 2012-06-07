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

(* We want to substitute M for nth hyp. in term N0, provided that the current context is ctx. *)
Fixpoint subst_t_outer (M0: te_LF) (n: nat) (ctx: ctx_LF) (N0: te_LF) {struct N0} :=
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
  If ctx = curr then (subst_t_inner M n N curr) 
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

(* We want to substitute ctx1 for every occ. of ctx2; our current context is curr.
   We assume in subst_ctx_outer that curr <> ctx2 *)

(* len_old is used to calculate shift in new hypotheses, when we substitute for some bctx
   this should be set to 0 *)
Fixpoint subst_ctx_outer (M0 : te_LF) (curr:ctx_LF) (ctx1: ctx_LF) (ctx2: ctx_LF) (len_old: nat) :=
match M0 with 
| hyp_LF n => hyp_LF n

| lam_LF A M => lam_LF A (subst_ctx_outer M curr ctx1 ctx2 len_old)

| appl_LF M N => appl_LF (subst_ctx_outer M curr ctx1 ctx2 len_old) 
                         (subst_ctx_outer N curr ctx1 ctx2 len_old)
| box_LF M => 
  let w0 := var_gen (free_worlds_LF M \u (var_from ctx1) \u 
                     (var_from ctx2) \u (var_from curr)) in
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
    box_LF (subst_ctx_outer M (fctx w0) ctx1' ctx2' len_old)

| unbox_fetch_LF w M => 
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => unbox_fetch_LF ctx1 (subst_ctx_new M ctx1 ctx2 len_old)
  | right _ =>
    match (eq_ctx_LF_dec w ctx2) with
    | left _ => unbox_fetch_LF ctx2 (subst_ctx_old M ctx1 ctx2 len_old)
    | right _ => unbox_fetch_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
    end
  end

| get_here_LF w M =>
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => get_here_LF w (subst_ctx_new M ctx1 ctx2 len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => get_here_LF w (subst_ctx_old M ctx1 ctx2 len_old)
      | right _ => get_here_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
    end
  end

| letdia_get_LF w M N =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in
  let curr' := recalc_simpl_ctx curr in
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => letdia_get_LF w (subst_ctx_new M ctx1 ctx2 len_old) 
                              (subst_ctx_outer N curr' ctx1' ctx2' len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
    | left _ => letdia_get_LF w (subst_ctx_old M ctx1 ctx2 len_old) 
                                (subst_ctx_outer N curr' ctx1' ctx2' len_old)
    | right _ => 
          letdia_get_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)  
                          (subst_ctx_outer N curr' ctx1' ctx2' len_old)
    end
  end
end
(* In subst_ctx_old we assume that current context was ctx2, now changed to ctx1 *)
with subst_ctx_old (M0 : te_LF) (ctx1: ctx_LF) (ctx2: ctx_LF) (len_old: nat) :=
match M0 with 
| hyp_LF n => hyp_LF n

| lam_LF A M => lam_LF A (subst_ctx_old M ctx1 ctx2 (len_old))

| appl_LF M N => appl_LF (subst_ctx_old M ctx1 ctx2 len_old) 
                         (subst_ctx_old N ctx1 ctx2 len_old)

| box_LF M =>
  let w0 := var_gen (free_worlds_LF M \u (var_from ctx1) \u (var_from ctx2)) in
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in     
    box_LF (subst_ctx_outer M (fctx w0) ctx1' ctx2' len_old)

| unbox_fetch_LF w M =>
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => unbox_fetch_LF w (subst_ctx_new M ctx1 ctx2 len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with 
      | left _ => unbox_fetch_LF w (subst_ctx_old M ctx1 ctx2 len_old)
      | right _ => unbox_fetch_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
    end
  end 

| get_here_LF w M =>
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => get_here_LF w (subst_ctx_new M ctx1 ctx2 len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => get_here_LF w (subst_ctx_old M ctx1 ctx2 len_old)
      | right _ => get_here_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
    end
   end

| letdia_get_LF w M N =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in
  let N' := subst_ctx_old N ctx1' ctx2' len_old in
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => letdia_get_LF w (subst_ctx_new M ctx1 ctx2 len_old) N'
  | right _ =>
    match (eq_ctx_LF_dec w ctx2) with
    | left _ => letdia_get_LF w (subst_ctx_old M ctx1 ctx2 len_old) N'
    | right _ => letdia_get_LF w (subst_ctx_outer M w ctx1 ctx2 len_old) N'
    end
  end
end
(* In subst_ctx_new we assume that current context is ctx1 *)
with subst_ctx_new (M0 : te_LF) (ctx1: ctx_LF) (ctx2: ctx_LF) (len_old: nat) :=
match M0 with 

| hyp_LF n => 
  match ctx2 with
    | bctx _ => hyp_LF n
    | fctx _ => hyp_LF (len_old+n)
  end

| lam_LF A M => lam_LF A (subst_ctx_new M ctx1 ctx2 len_old)

| appl_LF M N => appl_LF (subst_ctx_new M ctx1 ctx2 len_old) 
                         (subst_ctx_new N ctx1 ctx2 len_old)

| box_LF M =>
  let w0 := var_gen (free_worlds_LF M \u (var_from ctx1) \u (var_from ctx2)) in
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
    box_LF (subst_ctx_outer M (fctx w0) ctx1' ctx2' len_old)

| unbox_fetch_LF w M =>
  match (eq_ctx_LF_dec w ctx1) with
    | left _ => unbox_fetch_LF w (subst_ctx_new M ctx1 ctx2 len_old)
    | right _ => 
      match (eq_ctx_LF_dec w ctx2) with 
        | left _ => unbox_fetch_LF ctx1 (subst_ctx_old M ctx1 ctx2 len_old)
        | right _ => unbox_fetch_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
      end
  end

| get_here_LF w M =>
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => get_here_LF w (subst_ctx_new M ctx1 ctx2 len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => get_here_LF ctx1 (subst_ctx_old M ctx1 ctx2 len_old)
      | right _ => get_here_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
    end
   end

| letdia_get_LF w M N =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => letdia_get_LF w (subst_ctx_new M ctx1 ctx2 len_old) 
                              (subst_ctx_old N ctx1' ctx2' len_old)
  | right _ =>
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => letdia_get_LF ctx1 (subst_ctx_old M ctx1 ctx2 len_old) 
                                     (subst_ctx_old N ctx1' ctx2' len_old) 
      | right _ => letdia_get_LF w (subst_ctx_outer M w ctx1 ctx2 len_old) 
                                   (subst_ctx_old N ctx1' ctx2' len_old) 
    end
  end 
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
      subst_ctx_outer M curr c1 c2 len_old.

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
  subst_ctx_outer M curr c1 c2 len_old = {{ c1 // c2 }} [M | curr, len_old].
intros;
unfold subst_ctx;
repeat case_if;
reflexivity.
Qed.

Lemma generate_fresh:
forall M w
  (HIn: w \in M),
  var_gen M <> w.
Admitted.

Lemma no_unbound_worlds_LF_subst_w_id:
forall M n
  (H_unbound: unbound_worlds n M = nil),
  forall w w0, {{ w // bctx n }} [M | w0, 0] = M.
induction M; intros; unfold subst_ctx.
(* hyp *)
repeat case_if; reflexivity.
(* lam *)
unfold subst_ctx in *;
simpl in H_unbound.
specialize IHM with n w w0.
apply IHM with (w:=w) (w0:=w0) in H_unbound.
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
inversion H_unbound; subst.
apply IHM with (w:=w) (w0:=w0) in H0. 
repeat case_if; simpl; try subst; auto.
destruct w.
rewrite subst_ctx__outer;
unfold recalc_simpl_ctx; try discriminate;
assert ({{bctx (S n0) // bctx (S n)}}[M
     | fctx (var_gen (free_worlds_LF M \u var_from (bctx n0) \u \{})), 0] = M) by
  (eapply IHM with (n:=S n); simpl in H_unbound; assumption).
rewrite H2; reflexivity.
intro nn; inversion nn; subst n0; elim H; reflexivity.
subst w0;
rewrite subst_ctx__outer;
unfold recalc_simpl_ctx; try discriminate.
rewrite IHM; eauto.
assert (v \in free_worlds_LF M \u var_from (fctx v) \u \{}).
repeat rewrite in_union; right; left; simpl; rewrite in_singleton; reflexivity.
intro. inversion H2. symmetry in H4.
eapply generate_fresh; eauto. 
subst w0; destruct w.
rewrite subst_ctx__outer;
unfold recalc_simpl_ctx; try discriminate.
assert ({{bctx (S n0) // bctx (S n)}}[M
     | fctx (var_gen (free_worlds_LF M \u var_from (bctx n0) \u \{})), 0] = M) by
  (eapply IHM with (n:=S n); simpl in H_unbound; assumption).
rewrite H2; reflexivity.
intro nn; inversion nn; subst n0; elim H; reflexivity.
rewrite subst_ctx__outer;
unfold recalc_simpl_ctx; try discriminate.
rewrite IHM; eauto.
assert (v \in free_worlds_LF M \u var_from (fctx v) \u \{}).
repeat rewrite in_union; right; left; simpl; rewrite in_singleton; reflexivity.
intro. inversion H3. symmetry in H5.
eapply generate_fresh; eauto. 
destruct w.
rewrite subst_ctx__outer;
unfold recalc_simpl_ctx; try discriminate.
rewrite IHM; eauto.
intro nn; inversion nn; subst n0; elim H; reflexivity.
rewrite subst_ctx__outer;
unfold recalc_simpl_ctx; try discriminate.
rewrite IHM; eauto.
assert (v \in free_worlds_LF M \u var_from (fctx v) \u \{} \u var_from w0).
repeat rewrite in_union; right; left; simpl; rewrite in_singleton; reflexivity.
intro. inversion H4. symmetry in H6.
eapply generate_fresh; eauto. 
(* unbox_fetch *)
inversion H_unbound; destruct c; simpl; try discriminate.
repeat case_if; simpl;
try rewrite subst_ctx__old;
try rewrite subst_ctx__new;
try rewrite subst_ctx__outer;
try discriminate;
try rewrite IHM; 
eauto.
subst w; reflexivity.
(* get_here *)
inversion H_unbound; destruct c; simpl; try discriminate.
repeat case_if; simpl;
try rewrite subst_ctx__old;
try rewrite subst_ctx__new;
try rewrite subst_ctx__outer;
try discriminate;
try rewrite IHM; 
eauto.
(* letdia_get *)
inversion H_unbound; destruct c; simpl; try discriminate.
apply app_eq_nil in H0; destruct H0.
repeat case_if; simpl;
unfold recalc_simpl_ctx in *; 
destruct w; destruct w0;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__outer;
try discriminate;
try rewrite IHM1;
try rewrite IHM2; 
eauto;
try (intro nn; inversion nn; subst; elim H1; reflexivity);
try (intro nn; inversion nn; subst; elim H3; reflexivity).
intro nn; inversion nn; subst; elim H2; reflexivity.
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

End Lemmas.

Close Scope label_free_is5_scope.