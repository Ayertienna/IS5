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
| hyp_LF n => 
    hyp_LF n
| lam_LF A M => 
    lam_LF A (subst_t_outer M0 n ctx M curr)
| appl_LF M N => 
    appl_LF (subst_t_outer M0 n ctx M curr) (subst_t_outer M0 n ctx M curr)
| box_LF M => 
  let w0 := var_gen (free_worlds_LF N0) in (* shouldn't we add sth? *)
    box_LF (subst_t_outer M0 n ctx M (fctx w0))
| unbox_fetch_LF w M => 
  match (eq_ctx_LF_dec ctx w) with
    | left _ => unbox_fetch_LF w (subst_t_inner M0 n M ctx) 
    | right _ => unbox_fetch_LF w (subst_t_outer M0 n ctx M w)
  end
| get_here_LF w M =>
  match (eq_ctx_LF_dec ctx w) with
    | left _ => get_here_LF w (subst_t_inner M0 n M ctx) 
    | right _ => get_here_LF w (subst_t_outer M0 n ctx M w)
  end
| letdia_get_LF w M N =>
  match (eq_ctx_LF_dec ctx w) with
    | left _ => letdia_get_LF w (subst_t_inner M0 n M ctx) (subst_t_outer M0 n ctx N w)
    | right _ => letdia_get_LF w (subst_t_outer M0 n ctx M w) (subst_t_outer M0 n ctx N w)
  end
end
(* Current context is exactly the context in which we want to do susbtitution *)
with subst_t_inner (M0: te_LF) (m: nat) (N0: te_LF) (curr: ctx_LF) {struct N0} :=
match N0 with
| hyp_LF n => 
    if (eq_nat_dec n m) then M0 else hyp_LF n
| lam_LF A M => 
    lam_LF A (subst_t_inner M0 m M curr)
| appl_LF M N => 
    appl_LF (subst_t_inner M0 m M curr) (subst_t_inner M0 m N curr)
| box_LF M =>
  let w0 := var_gen (free_worlds_LF N0) in
    box_LF (subst_t_outer M0 m curr M (fctx w0))
| unbox_fetch_LF w M =>
  match (eq_ctx_LF_dec curr w) with
    | left _ => unbox_fetch_LF w (subst_t_inner M0 m M curr) 
    | right _ => unbox_fetch_LF w (subst_t_outer M0 m curr M w)
  end
| get_here_LF w M =>
  match (eq_ctx_LF_dec curr w) with
    | left _ => get_here_LF w (subst_t_inner M0 m M curr) 
    | right _ => get_here_LF w (subst_t_outer M0 m curr M w)
  end
| letdia_get_LF w M N =>
  match (eq_ctx_LF_dec curr w) with
    | left _ => letdia_get_LF w (subst_t_inner M0 m M curr) (subst_t_outer M0 m curr N w)
    | right _ => letdia_get_LF w (subst_t_outer M0 m curr M w) (subst_t_outer M0 m curr N w)
  end
end.

Definition subst_t M n ctx N curr :=
  If ctx = curr then (subst_t_inner M n N curr) 
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
  let w0 := var_gen (free_worlds_LF M) in
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
  match (eq_ctx_LF_dec w ctx2) with
    | left _ => unbox_fetch_LF w (subst_ctx_old M ctx1 ctx2 len_old)
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
match (eq_ctx_LF_dec c1 c2) with
| left _ => M
| right _ => 
  match (eq_ctx_LF_dec curr c1) with
  | left _ => subst_ctx_new M c1 c2 len_old
  | right _ => 
    match (eq_ctx_LF_dec curr c2) with
    | left _ => subst_ctx_old M c1 c2 len_old
    | right _ => subst_ctx_outer M curr c1 c2 len_old
    end
  end
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


Lemma subst_ctx_rewrite_new:
forall w0 w1 k M, 
  {{ w0 // w1}}[ {{w1 // k}} [M | w1, 0] | w1, 0] = {{ w0 // k }} [M | w0, 0]. 
Admitted.

Lemma subst_ctx_rewrite_old:
forall w0 w1 k M, 
  {{ w0 // w1}}[ {{w1 // k}} [M | w1, 0] | w1, 0] = {{ w0 // k }} [M | w0, 0]. 
Admitted.

Lemma subst_ctx_rewrite_outer:
forall w0 w1 w k l M, 
  {{ w0 // w1}}[ {{w1 // k}} [M | w, 0] | w, l] = {{ w0 // k }} [M | w, 0]. 
Admitted.

End Lemmas.

Close Scope label_free_is5_scope.