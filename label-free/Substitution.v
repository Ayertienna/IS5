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

(* We want to substitute M for nth hyp. in term N0, provided that the current context
   is ctx. *)
Fixpoint subst_t_outer (M0: te_LF) (n: nat) (ctx: ctx_LF) (N0: te_LF) (curr: ctx_LF) {struct N0} :=
match N0 with
| hyp_LF n => hyp_LF n
| lam_LF A M => lam_LF A (subst_t_outer M0 n ctx M curr)
| appl_LF M N => appl_LF (subst_t_outer M0 n ctx M curr) (subst_t_outer M0 n ctx M curr)
| box_LF M => 
  let w0 := var_gen (free_worlds_LF N0) in (* shouldn't we add sth? *)
    box_LF (subst_t_outer M0 n ctx M (fctx w0))
| unbox_LF M => unbox_LF (subst_t_outer M0 n ctx M curr)
| unbox_fetch_LF w M => 
  match (eq_ctx_LF_dec ctx w) with
    | left _ => unbox_fetch_LF w (subst_t_inner M0 n M ctx) 
    | right _ => unbox_fetch_LF w (subst_t_outer M0 n ctx M w)
  end
| here_LF M => here_LF (subst_t_outer M0 n ctx M curr)
| get_here_LF w M =>
  match (eq_ctx_LF_dec ctx w) with
    | left _ => get_here_LF w (subst_t_inner M0 n M ctx) 
    | right _ => get_here_LF w (subst_t_outer M0 n ctx M w)
  end
| letdia_LF M N => letdia_LF (subst_t_outer M0 n ctx M curr) (subst_t_outer M0 n ctx N curr)
| letdia_get_LF w M N =>
  match (eq_ctx_LF_dec ctx w) with
    | left _ => letdia_get_LF w (subst_t_inner M0 n M ctx) (subst_t_outer M0 n ctx N w)
    | right _ => letdia_get_LF w (subst_t_outer M0 n ctx M w) (subst_t_outer M0 n ctx N w)
  end
end
(* Current context is exactly the context in which we want to do susbtitution *)
with subst_t_inner (M0: te_LF) (m: nat) (N0: te_LF) (curr: ctx_LF) {struct N0} :=
match N0 with
| hyp_LF n => if (eq_nat_dec n m) then M0 else hyp_LF n
| lam_LF A M => lam_LF A (subst_t_inner M0 m M curr)
| appl_LF M N => appl_LF (subst_t_inner M0 m M curr) (subst_t_inner M0 m N curr)
| box_LF M =>
  let w0 := var_gen (free_worlds_LF N0) in
    box_LF (subst_t_outer M0 m curr M (fctx w0))
| unbox_LF M => unbox_LF (subst_t_inner M0 m M curr)
| unbox_fetch_LF w M =>
  match (eq_ctx_LF_dec curr w) with
    | left _ => unbox_fetch_LF w (subst_t_inner M0 m M curr) 
    | right _ => unbox_fetch_LF w (subst_t_outer M0 m curr M w)
  end
| here_LF M => here_LF (subst_t_inner M0 m M curr)
| get_here_LF w M =>
  match (eq_ctx_LF_dec curr w) with
    | left _ => get_here_LF w (subst_t_inner M0 m M curr) 
    | right _ => get_here_LF w (subst_t_outer M0 m curr M w)
  end
| letdia_LF M N => letdia_LF (subst_t_inner M0 m M curr) (subst_t_inner M0 m N curr)
| letdia_get_LF w M N =>
  match (eq_ctx_LF_dec curr w) with
    | left _ => letdia_get_LF w (subst_t_inner M0 m M curr) (subst_t_outer M0 m curr N w)
    | right _ => letdia_get_LF w (subst_t_outer M0 m curr M w) (subst_t_outer M0 m curr N w)
  end
end.

Definition subst_t M n ctx N curr :=
  if (eq_ctx_LF_dec ctx curr) then (subst_t_inner M n N curr) 
  else (subst_t_outer M n ctx N curr). 

Notation " [ M // n | ctx ] [ N | curr ] " := 
  (subst_t M n ctx N curr) (at level 5) : label_free_is5_scope.

Fixpoint subst_list L n N subst_ctx curr_ctx :=
match L with
| nil => N
| M :: L' => [M//n | subst_ctx] 
             [subst_list L' (S n) N subst_ctx curr_ctx | curr_ctx]
end.

(* Context substitution *)

Definition recalculate_ctx (ctx1: ctx_LF) (ctx2: ctx_LF) : prod ctx_LF ctx_LF :=
   match ctx1, ctx2 with
      | fctx w1', bctx w2' => (ctx1, bctx (S w2'))
      | fctx w1', fctx w2' => (ctx1, ctx2)
      | bctx w1', bctx w2' => (bctx (S w1'), bctx (S w2'))
      | bctx w1', fctx w2' => (bctx (S w1'), ctx2)
   end.

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
  let w0 := var_gen ((free_worlds_LF M) \u (var_from curr) \u (var_from ctx1) \u (var_from ctx2)) in
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
    box_LF (subst_ctx_outer M (fctx w0) ctx1' ctx2' len_old)
| unbox_LF M => unbox_LF (subst_ctx_outer M curr ctx1 ctx2 len_old)
| unbox_fetch_LF w M =>
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => unbox_fetch_LF w (subst_ctx_new M ctx1 ctx2 len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => unbox_fetch_LF w (subst_ctx_old M ctx1 ctx2 len_old)
      | right _ => unbox_fetch_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
    end
   end
| here_LF M => here_LF (subst_ctx_outer M curr ctx1 ctx2 len_old)
| get_here_LF w M =>
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => get_here_LF w (subst_ctx_new M ctx1 ctx2 len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => get_here_LF w (subst_ctx_old M ctx1 ctx2 len_old)
      | right _ => get_here_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
    end
   end
| letdia_LF M N =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
    letdia_LF (subst_ctx_outer M curr ctx1 ctx2 len_old)
              (subst_ctx_outer N curr ctx1' ctx2' len_old)
| letdia_get_LF w M N =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => letdia_get_LF w (subst_ctx_new M ctx1 ctx2 len_old) 
                              (subst_ctx_outer N curr ctx1' ctx2' len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => letdia_get_LF w (subst_ctx_old M ctx1 ctx2 len_old) 
                                  (subst_ctx_outer N curr ctx1' ctx2' len_old)
      | right _ => letdia_get_LF w (subst_ctx_outer M w ctx1 ctx2 len_old) 
                                   (subst_ctx_outer N curr ctx1' ctx2' len_old)
    end
   end
end
(* In subst_ctx_old we assume that current context is ctx2 *)
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
| unbox_LF M => unbox_LF (subst_ctx_old M ctx1 ctx2 len_old)
| unbox_fetch_LF w M =>
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => unbox_fetch_LF ctx1 (subst_ctx_new M ctx1 ctx2 len_old)
  | right _ => unbox_fetch_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
   end
| here_LF M => here_LF (subst_ctx_old M ctx1 ctx2 len_old)
| get_here_LF w M =>
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => get_here_LF ctx1 (subst_ctx_new M ctx1 ctx2 len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => get_here_LF w (subst_ctx_old M ctx1 ctx2 len_old)
      | right _ => get_here_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
    end
   end
| letdia_LF M N => 
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
    letdia_LF (subst_ctx_old M ctx1 ctx2 len_old) 
              (subst_ctx_old N ctx1' ctx2' len_old)
| letdia_get_LF w M N =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => letdia_get_LF ctx1 (subst_ctx_new M ctx1 ctx2 len_old) (subst_ctx_old M ctx1' ctx2' len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => letdia_get_LF w (subst_ctx_old M ctx1 ctx2 len_old) (subst_ctx_old M ctx1' ctx2' len_old) 
      | right _ => letdia_get_LF w (subst_ctx_outer M w ctx1 ctx2 len_old) (subst_ctx_old M ctx1' ctx2' len_old) 
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
| unbox_LF M => unbox_LF (subst_ctx_new M ctx1 ctx2 len_old)
| unbox_fetch_LF w M =>
  match (eq_ctx_LF_dec w ctx2) with
    | left _ => unbox_fetch_LF ctx1 (subst_ctx_old M ctx1 ctx2 len_old)
    | right _ => unbox_fetch_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
  end
| here_LF M => here_LF (subst_ctx_new M ctx1 ctx2 len_old)
| get_here_LF w M =>
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => get_here_LF w (subst_ctx_new M ctx1 ctx2 len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => get_here_LF ctx1 (subst_ctx_old M ctx1 ctx2 len_old)
      | right _ => get_here_LF w (subst_ctx_outer M w ctx1 ctx2 len_old)
    end
   end
| letdia_LF M N => 
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
    letdia_LF (subst_ctx_new M ctx1 ctx2 len_old) 
              (subst_ctx_new N ctx1' ctx2' len_old)
| letdia_get_LF w M N =>
  let (ctx1', ctx2') := recalculate_ctx ctx1 ctx2 in 
  match (eq_ctx_LF_dec w ctx1) with
  | left _ => letdia_get_LF w (subst_ctx_new M ctx1 ctx2 len_old) (subst_ctx_old M ctx1' ctx2' len_old)
  | right _ => 
    match (eq_ctx_LF_dec w ctx2) with
      | left _ => letdia_get_LF ctx1 (subst_ctx_old M ctx1 ctx2 len_old) (subst_ctx_old M ctx1' ctx2' len_old) 
      | right _ => letdia_get_LF w (subst_ctx_outer M w ctx1 ctx2 len_old) (subst_ctx_old M ctx1' ctx2' len_old) 
    end
  end
end.

Definition subst_ctx M c1 c2 curr len_old :=
match (eq_ctx_LF_dec c1 c2) with
| left _ => M
| right _ => 
  if (eq_ctx_LF_dec curr c1) then subst_ctx_new M c1 c2 len_old
  else if (eq_ctx_LF_dec curr c2) then subst_ctx_old M c1 c2 len_old
       else subst_ctx_outer M curr c1 c2 len_old
end.

Notation " {{ c1 // c2 }} [ M | curr , m ] " := 
  (subst_ctx M c1 c2 curr m) (at level 5) : label_free_is5_scope.

Definition open_ctx M ctx curr := subst_ctx M ctx (bctx 0) curr 0.

Notation " M ^^ [ w | w' ] " := (open_ctx M w w') (at level 10) : label_free_is5_scope.


Section Lemmas.

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


(*
Lemma no_unbound_worlds_subst_w_id:
forall M w k w'
  (H_unbound: unbound_worlds k M = nil),
  {{w//bctx k}}[M | w', 0] = M.
intros;
generalize dependent w;
generalize dependent k;
induction M; unfold subst_ctx in *;
intros.
(* hyp *)
repeat case_if; reflexivity.
(* lam *)
apply IHM with (w:=w) in H_unbound;
repeat case_if; simpl;
try rewrite H_unbound; reflexivity.
(* appl *)
simpl in H_unbound;
apply app_eq_nil in H_unbound;
destruct H_unbound as (H_Un1, H_Un2);
apply IHM1 with (w:=w) in H_Un1;
apply IHM2 with (w:=w) in H_Un2;
repeat case_if; simpl;
try (rewrite H_Un1; rewrite H_Un2); reflexivity.
(* box *)

Admitted.

Lemma closed_w_subst_id:
forall M w n w'
  (HT: lc_w_n_LF M n),
  {{w//bctx n}} [M | w', 0] = M.
intros;
apply no_unbound_worlds_subst_w_id;
apply closed_no_unbound_worlds;
assumption.
Qed.

Lemma subst_order_irrelevant:
forall N M n m w w' w''
  (H_LC: lc_w_LF M),
  subst_ctx ([M//n | w''] [N | w']) w (bctx m) w' 0 = 
  [M//n | w''] [(subst_ctx N w (bctx m) w' 0) | w'].
Admitted.

Lemma subst_w_comm:
forall M w w' w'' n w0 w1 k
  (Neq: w'' <> w),
  {{fctx w'//fctx w''}}[({{fctx w//bctx n}}[M | w0, 0]) | w1, k] = {{fctx w//bctx n}}[({{fctx w'//fctx w''}}[M | w1, k]) | w0, 0].
Admitted.
*)

Lemma var_gen_neq:
  forall w S
  (HT: w \in S),
  fctx w <> fctx (var_gen S).
intros; intro; inversion H; subst;
assert (var_gen S \notin S) by apply var_gen_spec;
contradiction.
Qed.

Ltac in_singleton_union :=
match goal with
| |- ?w \in \{?w} => rewrite in_singleton; reflexivity
| |- ?w \in \{?w} \/ _ => left; in_singleton_union
| |- _ \/ ?w \in \{?w} => right; in_singleton_union
| |- _ \/ ?w \in \{?w} \/ _ => right; in_singleton_union
| |- _ \/ _ \/ ?w \in \{?w}  => right; in_singleton_union
| _ => fail
end.

Ltac autorewrite_ctx :=
match goal with 
| [H : (bctx ?n = bctx ?n') |- _ ] => rewrite H
| [H : (fctx ?n = fctx ?n') |- _ ] => rewrite H
| _ => skip
end.

Lemma subst_id:
forall M w n w0 w0' k
  (HT: w \notin (free_worlds_LF M)),
  {{bctx n // fctx w}}[ {{fctx w // bctx n}} [M | fctx w0', 0] | fctx w0, k] = M.
intros;
generalize dependent n;
generalize dependent w0';
generalize dependent w0;
induction M; intros.
(* hyp *)
unfold subst_ctx;
simpl in *;
repeat case_if;
reflexivity.
(* lam *)
simpl in HT;
unfold subst_ctx;
repeat case_if; 
subst; simpl in *;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__outer;
auto;
rewrite IHM; auto.
(* appl *)
simpl in HT; rewrite notin_union in HT; destruct HT;
unfold subst_ctx;
repeat case_if;
subst; simpl in *;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__outer;
auto;
try rewrite IHM1; try rewrite IHM2; auto.
(* box *)
simpl in HT;
unfold subst_ctx;
repeat case_if;
subst; simpl in *;
try repeat rewrite subst_ctx__outer;
try rewrite IHM; 
try discriminate;
try (apply var_gen_neq;
  repeat rewrite in_union; right; 
  in_singleton_union);
auto.
(* unbox *)
simpl in HT;
unfold subst_ctx;
repeat case_if;
subst; simpl in *;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__outer;
try rewrite IHM; 
try discriminate;
auto.
(* unbox_fetch *)
simpl in HT; destruct c; simpl in HT;
try (rewrite notin_union in HT; destruct HT);
unfold subst_ctx;
repeat (case_if; simpl);
subst; simpl in *;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__outer;
try rewrite IHM; 
autorewrite_ctx;
try discriminate;
auto;
autorewrite_ctx.
(* here *)
simpl in HT;
unfold subst_ctx;
repeat case_if;
subst; simpl in *;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__outer;
try rewrite IHM; 
try discriminate;
auto.
(* get_here *)
simpl in HT; destruct c; simpl in HT;
try (rewrite notin_union in HT; destruct HT);
unfold subst_ctx;
repeat (case_if; simpl);
subst; simpl in *;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__outer;
try rewrite IHM; 
autorewrite_ctx;
try discriminate;
auto;
autorewrite_ctx.
(* letdia *)
simpl in HT;
unfold subst_ctx;
repeat case_if;
subst; simpl in *;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__outer;
try rewrite IHM1;
try rewrite IHM2; 
try discriminate;
auto.
(* letdia_get *)
simpl in HT; destruct c; simpl in HT;
try (rewrite notin_union in HT; destruct HT);
unfold subst_ctx;
repeat (case_if; simpl);
subst; simpl in *;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__outer;
try rewrite IHM1;
try rewrite IHM2; 
autorewrite_ctx;
try discriminate;
auto;
autorewrite_ctx.
Qed.

(* This is just one option of neutral substitution! *)
Lemma subst_neutral:
forall M w w' n k
  (HT: lc_w_n_LF M n),
  {{fctx w//bctx n}}[({{bctx n//fctx w'}}[M | fctx w', k]) | fctx w, 0] = {{fctx w//fctx w'}}[ M | fctx w', k].
Admitted.

Lemma subst_neutral':
forall M w w' n  k
  (HT: lc_w_n_LF M n),
  {{fctx w//bctx n}}[({{bctx n//fctx w'}}[M | fctx w, k]) | fctx w, 0] = {{fctx w//fctx w'}}[ M | fctx w, k].
Admitted.

Lemma subst_neutral'':
forall M w w' w0 n  k
  (HT: lc_w_n_LF M n),
  {{fctx w//bctx n}}[({{bctx n//fctx w'}}[M | fctx w0, k]) | fctx w0, 0] = {{fctx w//fctx w'}}[ M | fctx w0, k].
Admitted.

Lemma closed_step_opening:
forall M n w w0
  (HT: lc_w_n_LF M (S n)),
  lc_w_n_LF ({{fctx w//bctx n}}[M | w0, 0]) n.
Admitted.

End Lemmas.

Close Scope label_free_is5_scope.