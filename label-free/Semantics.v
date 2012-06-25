(* TODO: imports are messed up now that there's a module *) 
Require Import Syntax.
Require Import Substitution.
Require Import Metatheory.
Require Import LibList.
Require Import LibListSorted.
Require Import Arith.

Open Scope label_free_is5_scope.


Fixpoint ok A (G: list (var * A)) (Used: list var) : Prop :=
match G with 
| nil => True
| (w, Gamma) :: G => If Mem w Used then False else ok A G (w::Used)
end.

Definition ok_Bg (G: Background_LF) : Prop :=
ok (list (var * ty_LF)) G nil  /\
ok (ty_LF) (flat_map snd G) nil.

Global Reserved Notation " G '|=' Ctx '|-' M ':::' A " (at level 70).
 
(* Statics *)

Inductive types_LF: Background_LF -> Context_LF -> te_LF -> ty_LF -> Prop :=

| t_hyp_LF: forall A G w Gamma v
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT: Mem (v, A) Gamma),
  G |= (w, Gamma) |- hyp_LF (fvar v) ::: A

| t_lam_LF: forall L A B G w Gamma M
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT: forall v', v' \notin L -> 
    G |= (w, (v', A) :: Gamma) |- M ^t^ (hyp_LF (fvar v')) ::: B),
  G |= (w, Gamma) |- (lam_LF A M) ::: A ---> B

| t_appl_LF: forall A B G w Gamma M N
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT1: G |= (w, Gamma) |- M ::: A ---> B)
  (HT2: G |= (w, Gamma) |- N ::: A),
  G |= (w, Gamma) |- (appl_LF M N) ::: B

| t_box_LF: forall L A G w Gamma M
  (Ok_Bg: ok_Bg (G & (w, Gamma)))
  (HT: forall w', w' \notin L -> 
    G & (w, Gamma) |= (w', nil) |- M ^w^ (fctx w') ::: A),
  G |= (w, Gamma) |- box_LF M ::: [*] A

| t_unbox_LF: forall A G w Gamma M
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT: G |= (w, Gamma) |- M ::: [*] A),
  G |= (w, Gamma) |- unbox_fetch_LF (fctx w) M ::: A

| t_unbox_fetch_LF: forall A G w Gamma w' Gamma' M
  (Ok_Bg: ok_Bg ((w, Gamma) :: G & (w', Gamma')))
  (HT: (G & (w', Gamma')) |= (w, Gamma) |- M ::: [*] A),
  forall G', permut (G & (w, Gamma)) G' ->
    G' |= (w', Gamma') |- unbox_fetch_LF (fctx w) M ::: A

| t_here_LF: forall A G w Gamma M
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma) |- get_here_LF (fctx w) M ::: <*> A

| t_get_here_LF: forall A G w Gamma Ctx' M
  (Ok_Bg: ok_Bg ((w, Gamma) :: G & Ctx'))
  (HT: G & Ctx' |= (w, Gamma) |- M ::: A),
  forall G', permut (G & (w, Gamma)) G' -> 
    G' |= Ctx' |- get_here_LF (fctx w) M ::: <*> A

| t_letdia_LF: forall L_w L_t A B G w Gamma M N
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT1: G |= (w, Gamma) |- M ::: <*> A)
  (HT2: forall v', v' \notin L_t -> forall w', w' \notin L_w ->
    (w', (v', A) :: nil) :: G |= 
      (w, Gamma) |- (N ^w^ (fctx w')) ^t^ (hyp_LF (fvar v')) ::: B),
  G |= (w, Gamma) |- letdia_get_LF (fctx w) M N ::: B 

| t_letdia_get_LF: forall L_w L_t A B G w Gamma Ctx' M N
  (Ok_Bg: ok_Bg ((w, Gamma) :: G & Ctx'))
  (HT1: G & Ctx' |= (w, Gamma) |- M ::: <*> A)
  (HT2: forall v', v' \notin L_t -> forall w', w' \notin L_w ->
    (w', ((v', A) :: nil)) :: G & (w, Gamma) |= 
      Ctx' |- (N ^w^ (fctx w')) ^t^ (hyp_LF (fvar v')) ::: B),
  forall G0, permut (G & (w, Gamma)) G0 -> 
    G0 |= Ctx' |- letdia_get_LF (fctx w) M N ::: B
where " G '|=' Ctx '|-' M ':::' A " := (types_LF G Ctx M A) : label_free_is5_scope.


(* Dynamics *)

Inductive value_LF: te_LF -> Prop :=
| val_lam_LF: forall A M, value_LF (lam_LF A M)
| val_box_LF: forall M, value_LF (box_LF M)
| val_get_here_LF: forall M Ctx, value_LF M -> value_LF (get_here_LF Ctx M)
.

Global Reserved Notation " M |-> N " (at level 70).

Inductive step_LF: (te_LF * ctx_LF) -> (te_LF * ctx_LF) -> Prop :=
| red_appl_lam_LF: forall ctx M A N,
  lc_w_LF M -> lc_t_n_LF M 1 ->
  lc_w_LF N -> lc_t_LF N ->
  (appl_LF (lam_LF A M) N, ctx) |-> ( M ^t^ N , ctx)

| red_unbox_fetch_box_LF: forall ctx ctx' M,
  lc_w_n_LF M 1 -> lc_t_LF M ->
  (unbox_fetch_LF ctx' (box_LF M), ctx) |-> (M ^w^ ctx, ctx)

| red_letdia_get_get_here_LF: forall ctx ctx' ctx'' M N,
  lc_w_LF M -> lc_t_LF M ->
  lc_w_n_LF N 1 -> lc_t_n_LF N 1 ->
  (letdia_get_LF ctx' (get_here_LF ctx'' M) N, ctx) |-> ((N ^w^ ctx'') ^t^ M, ctx)

| red_appl_LF: forall ctx M N M'
  (HT: (M, ctx) |-> (M', ctx)), 
  lc_w_LF M -> lc_t_LF M ->
  lc_w_LF N -> lc_t_LF N ->
  (appl_LF M N, ctx) |-> (appl_LF M' N, ctx)

| red_unbox_fetch_LF: forall ctx' M M' ctx
  (HT: (M, ctx') |-> (M', ctx')), 
  lc_w_LF M -> lc_t_LF M ->
  (unbox_fetch_LF ctx' M, ctx) |-> (unbox_fetch_LF ctx' M', ctx)

| red_get_here_LF: forall ctx ctx' M M' 
  (HT: (M, ctx) |-> (M', ctx)), 
  lc_w_LF M -> lc_t_LF M ->
  (get_here_LF ctx M, ctx') |-> (get_here_LF ctx M', ctx')

| red_letdia_get_LF: forall ctx ctx' M N M'
  (HT: (M, ctx) |-> (M', ctx)), 
  lc_w_LF M -> lc_t_LF M ->
  lc_w_n_LF N 1 -> lc_t_n_LF N 1 ->
  (letdia_get_LF ctx M N, ctx') |-> (letdia_get_LF ctx M' N, ctx')

where " M |-> N " := (step_LF M N ) : label_free_is5_scope.

Section Lemmas.

Lemma Fresh: 
  forall (L:fset var), exists w0, w0 \notin L.
intro;
exists (var_gen L);
apply var_gen_spec.
Qed.

Lemma GlobalWeakening:
forall G G' Ctx Ctx' M A
  (HT: G ++ G' |= Ctx |- M ::: A),
  G & Ctx' ++ G' |= Ctx |- M ::: A.
Admitted.

Lemma WeakeningBackgroundElem:
forall G G' w Delta Delta' Ctx M A
  (HT: G & (w, Delta) ++ G' |= Ctx |- M ::: A),
  G & (w, Delta ++ Delta') ++ G' |= Ctx |- M ::: A.
Admitted.

Lemma Weakening:
forall G w Gamma Gamma' M A
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma ++ Gamma') |- M ::: A.
Admitted.

(* emptyEquiv = map (fun x => (x, nil)) (map fst G) *)
Fixpoint emptyEquiv (G: Background_LF) : Background_LF :=
match G with
| nil => nil
| (w, a)::G => (w, nil) :: emptyEquiv G
end.

Lemma types_weakened:
forall G w Gamma M A
  (HT: emptyEquiv G |= (w, nil) |- M ::: A),
  G |= (w, Gamma) |- M ::: A.
Admitted.

Lemma subst_t_preserv_types:
forall G w Gamma B M N v A
  (H_lc_t: lc_t_LF M)
  (H_lc_w: lc_w_LF M)
  (HT: G |= (w, Gamma) |- N ::: B), 
  (* "inner" substitution *)
  ( forall Gamma0,
    (* this should really be permutation... *)
    Gamma = (v, A) :: Gamma0 ->
    emptyEquiv G |= (w, nil) |- M ::: A ->
    G |= (w, Gamma0) |- [M // fvar v] N ::: B)
  /\
  (* "outer" substitution *)
  ( forall G0 G' G'' w' Gamma',
    permut G (G0 & (w', (v,A)::Gamma')) ->
    permut G' (G0 & (w, Gamma)) ->
    permut G'' (G0 & (w', Gamma')) ->
    emptyEquiv G' |= (w', nil) |- M ::: A ->
    G'' |= (w, Gamma) |- [M // fvar v] N ::: B).
intros.
remember (w, Gamma) as Ctx.
generalize dependent v;
generalize dependent A;
generalize dependent M;
generalize dependent w;
generalize dependent Gamma.
induction HT; split; intros;
inversion HeqCtx; subst;
simpl in *.
(* hyp *)
case_if.
inversion H; subst;
assert (A = A0) by skip; (* Ok_Bg + HT *)
subst; apply types_weakened; assumption.
constructor.
skip. (* ok_Bg *)
(* Mem part should be automated! *)
rewrite Mem_cons_eq in HT; destruct HT.
  inversion H1; subst; elim H; reflexivity.
  assumption.

case_if.
inversion H3; subst;
(* v = v0 ->
   Ok_Bg + H + H0 + HT -->
   v0 occurs both in Gamma0 and in G -->
   contradiction *)
skip.
constructor.
skip. (* ok_Bg *)
assumption.
(* lam *)
apply t_lam_LF with (L:=L \u \{v}).
skip. (* ok_Bg *)
intros.
rewrite notin_union in H0; rewrite notin_singleton in H0; destruct H0.
unfold open_var in *.
rewrite <- subst_var_comm.
eapply H; eauto.
skip. (* this should really be permutations *)
intro; elim H2; subst; auto.
auto.

apply t_lam_LF with (L:=L \u \{v}).
skip. (* ok_Bg *)
intros.
rewrite notin_union in H4; rewrite notin_singleton in H4; destruct H4.
unfold open_var in *.
rewrite <- subst_var_comm.
eapply H; eauto.
skip. (* empty equiv + permut *)
intro; subst; elim H5; auto.
auto.
(* appl *)
econstructor; [ skip | eapply IHHT1 | eapply IHHT2]; eauto.
econstructor; [ skip | eapply IHHT1 | eapply IHHT2]; eauto.
(* box *)
econstructor; [skip | intros].
unfold open_ctx.
rewrite <- subst_order_irrelevant_bound.
eapply H; eauto.
skip. (* form H1 + weakening + emptyEquiv_last *)
auto.

econstructor; [skip | intros].
unfold open_ctx.
rewrite <- subst_order_irrelevant_bound.
eapply H with (G'' := G'' & (w0, Gamma0)); eauto.
skip. (* H0 + H2 *)
skip. (* H3 + H1 + Weakening *)
auto.
(* unbox *)
econstructor; [skip | eapply IHHT]; eauto.
econstructor; [skip | eapply IHHT]; eauto.
(* unbox_fetch *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT; eauto.
skip. (* emptyEquiv + permut *)
assumption.

assert (w <> w0) by skip. (* from Ok_Bg *)
assert (w <> w'0) by skip. (* Ok_bg + H + H0 *) 
(* H0 + H + ok_Bg + w <> w'0 -->
   G & (w, Gamma) ~=~ G0 & (w'0, (v, A0) :: Gamma'0) -->
   exists GH, exists GT, G = GH & (w'0, (v,A0)::Gamma'0) ++ GT. *)
assert (exists GH, exists GT, G = GH & (w'0, (v, A0)::Gamma'0) ++ GT) by skip.
destruct H6 as (GH, H6); destruct H6 as (GT, H6).
apply t_unbox_fetch_LF with (G:=GH ++ GT & (w'0, Gamma'0)) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (w':=w'0) (Gamma':=Gamma'0)
                 (G0:=GH ++ GT & (w0, Gamma0)); eauto.
subst; permut_simpl.
subst; permut_simpl.
skip. (* emptyEquiv + permut *)
skip. (* H2 + H + H0 *)
(* here *)
econstructor; [skip | eapply IHHT]; eauto.
econstructor; [skip | eapply IHHT]; eauto.
(* get_here *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT; eauto.
skip. (* emptyEquiv + permut *)
assumption.

assert (w <> w0) by skip. (* from Ok_Bg *)
assert (w <> w') by skip. (* Ok_bg + H + H0 *) 
(* H0 + H + ok_Bg + w <> w'0 -->
   G & (w, Gamma) ~=~ G0 & (w'0, (v, A0) :: Gamma'0) -->
   exists GH, exists GT, G = GH & (w', (v,A0)::Gamma'0) ++ GT. *)
assert (exists GH, exists GT, G = GH & (w', (v, A0)::Gamma') ++ GT) by skip.
destruct H7 as (GH, H7); destruct H7 as (GT, H7).
apply t_get_here_LF with (G:=GH ++ GT & (w', Gamma')) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (w':=w') (Gamma':=Gamma')
                 (G0:=GH ++ GT & (w0, Gamma0)); eauto.
subst; permut_simpl.
subst; permut_simpl.
skip. (* emptyEquiv + permut *)
skip. (* H2 + H + H0 *)

(* letdia *)
eapply t_letdia_LF with (L_t := L_t \u \{v}); [skip | eapply IHHT | intros]; eauto.
unfold open_var in *. unfold open_ctx in *.
rewrite notin_union in H0; rewrite notin_singleton in H0; destruct H0.
rewrite <- subst_order_irrelevant_bound.
rewrite <- subst_var_comm.
eapply H; eauto.
skip. (* weakening + assumption *)
intro; subst; elim H3; auto.
assumption.
assumption.

eapply t_letdia_LF with (L_t := L_t \u \{v}); [skip | eapply IHHT | intros]; eauto.
unfold open_var in *. unfold open_ctx in *.
rewrite notin_union in H4; rewrite notin_singleton in H4; destruct H4.
rewrite <- subst_order_irrelevant_bound.
rewrite <- subst_var_comm.
eapply H with (G0:=(w'0, (v',A)::nil)::G0) (w'0:=w') (Gamma':=Gamma') (A0:=A0); eauto.
permut_simpl; auto.
permut_simpl; auto.
skip. (* weakening + assumption *)
intro; subst; elim H6; auto.
assumption.
assumption.

(* letdia_get *)
assert (w <> w0) by skip. (* from Ok_bg *)
eapply t_letdia_get_LF with (G:=G) (Gamma:=Gamma) (L_t := L_t \u \{v}); eauto.
skip. (* ok_Bg *)
eapply IHHT; eauto.
skip. (* permut + assumption *)
intros. 
unfold open_var in *; unfold open_ctx in *.
rewrite notin_union in H4; rewrite notin_singleton in H4; destruct H4.
rewrite <- subst_order_irrelevant_bound.
rewrite <- subst_var_comm.
eapply H; eauto.
skip. (* weakening + permut + assumption *)
intro; subst; elim H6; auto.
auto.
auto.

assert (w <> w0) by skip. (* from ok_Bg *)
destruct (eq_var_dec w w').
subst.
(* from ok_Bg + H0 + H1 *)
assert (Gamma = (v, A0) :: Gamma') by skip.
assert (G1 = G) by skip.
subst.
eapply t_letdia_get_LF with (G:=G) (Gamma:=Gamma') (L_t:=L_t \u \{v}); eauto.
skip. (* ok_Bg *)
eapply IHHT; eauto.
skip. (* permut + emptyEquiv *)
intros.
unfold open_var in *; unfold open_ctx in *.
rewrite notin_union in H7; rewrite notin_singleton in H7; destruct H7.
rewrite <- subst_order_irrelevant_bound.
rewrite <- subst_var_comm.
eapply H with (G0:=G & (w'0, (v', A)::nil) ) (w'1:=w') (Gamma'0:=Gamma'); eauto.
permut_simpl.
permut_simpl.
skip. (* Weakening + permut + assumption *)
auto.
auto.
auto.
apply permut_sym; auto.

(* w <> w' /\
   Ok Bg /\
   (G & (w, Gamma)) ~=~ G0
   G0 ~=~ (G1 & (w', (v, A0) :: Gamma')) -->
   G & (w, Gamma) ~=~ G1 & (w', (v,A0)::Gamma') -->
   exists GH, exists GT, G1 = GH & (w, Gamma) ++ GT *)
assert (exists GH, exists GT, G1 = GH & (w, Gamma) ++ GT) by skip.
destruct H7 as (GH, H7). destruct H7 as (GT, H7).
eapply t_letdia_get_LF with (G:=GH++GT & (w', Gamma')) (Gamma:=Gamma) (L_t:=L_t \u \{v}).
skip. (* ok_Bg *)
eapply IHHT with (G0:=GH++GT & (w0,Gamma0)) (Gamma':=Gamma'); eauto.
permut_simpl. skip. (* H7 + H0 + H1 *)
permut_simpl.
skip. (* permut + assumption *)
intros.
unfold open_var in *; unfold open_ctx in *.
rewrite notin_union in H8; rewrite notin_singleton in H8; destruct H8.
rewrite <- subst_order_irrelevant_bound.
rewrite <- subst_var_comm.
eapply H with (G0:=(w'0, (v', A) :: nil) :: (GH ++ GT) & (w, Gamma)) (Gamma':=Gamma'); eauto. 
subst; permut_simpl. skip. (* H7 + H0 + H1 *)
permut_simpl.
skip. (* Weakening + permut + assumption *)
auto.
auto.
auto.
skip. (* permut + permut_sym *)
Admitted. (* No more subgoals but non-instantiated existential variables *)

Lemma subst_t_preserv_types_inner:
forall G w Gamma A B M N v
  (H_lc_t: lc_t_LF M)
  (H_lc_w: lc_w_LF M)
  (HT: G |= (w, (v, A) :: Gamma) |- N ::: B)
  (HM: emptyEquiv G |= (w, nil) |- M ::: A),
  G |= (w, Gamma) |- [M//fvar v] N ::: B.
intros;
eapply subst_t_preserv_types with (Gamma := (v, A) :: Gamma); eauto.
Qed.  

Lemma subst_t_preserv_types_outer:
forall G0 G G' G'' w w' Gamma Gamma' A B M N v
  (H_lc_t: lc_t_LF M)
  (H_lc_w: lc_w_LF M)
  (G0G: permut G (G0 & (w', (v, A) :: Gamma')))
  (G0G': permut G' (G0 & (w, Gamma)))
  (G0G'': permut G'' (G0 & (w', Gamma')))
  (HM: emptyEquiv G' |= (w', nil) |- M ::: A)
  (HT: G |= (w, Gamma) |- N ::: B),
  G'' |= (w, Gamma) |- [M // fvar v] N ::: B.
intros; 
eapply subst_t_preserv_types; eauto. 
Qed.  

Lemma rename_w_preserv_types:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A),
  (* "new" substitution *)
  ( permut G (G' & (w', Gamma')) ->
    G' |= (w, Gamma ++ Gamma') |- {{ fctx w // fctx w' }} M ::: A) /\
  (* "old" substitution *)
  ( permut G (G' & (w', Gamma')) ->
    G' |= (w', Gamma' ++ Gamma) |- {{ fctx w' // fctx w }} M ::: A) /\
  (* "outer" substitution *)
  (forall G0 w'' Gamma'',
    permut G (G0 & (w', Gamma') & (w'', Gamma'')) ->
    permut G' (G0 & (w', Gamma' ++ Gamma'')) ->
    G' |= (w, Gamma) |- {{ fctx w' // fctx w''}} M ::: A).
intros;
remember (w, Gamma) as Ctx;
generalize dependent Gamma;
generalize dependent w;
generalize dependent w';
generalize dependent Gamma';
generalize dependent G';
induction HT; repeat split; intros;
inversion HeqCtx; subst;
simpl in *.
(* hyp *)
constructor;
[ skip | (* ok_Bg will need some lemmas later on *)
  rewrite Mem_app_or_eq; left; auto].
constructor;
[ skip | (* ok_Bg *)
  rewrite Mem_app_or_eq; right; auto].
constructor; 
[ skip | (* ok_Bg *) 
  auto].
(* lam *)
apply t_lam_LF with (L := L);
[ skip | (* ok_Bg *)
  intros]; unfold open_var in *;
rewrite subst_order_irrelevant_free;
try (eapply H with (v':=v') (G':=G') (Gamma := (v',A)::Gamma0));
eauto;
simpl; apply notin_empty. 
apply t_lam_LF with (L := L);
[ skip | (* ok_Bg *)
  intros]; unfold open_var in *;
rewrite subst_order_irrelevant_free;
edestruct H; eauto; destruct H3; 
replace ((v', A) :: Gamma' ++ Gamma0) with (Gamma' ++ (v', A) :: Gamma0)
  by skip; (* TODO: order of elems in context is irrelevant *)
eauto;
apply notin_empty. 
apply t_lam_LF with (L := L);
[ skip | (* ok_Bg *)
  intros]; unfold open_var in *;
rewrite subst_order_irrelevant_free;
edestruct H; eauto; destruct H4;
eauto;
simpl; apply notin_empty. 
(* appl *)
apply t_appl_LF with (A:=A);
[ skip |  (* ok_Bg *)
  apply IHHT1 with (Gamma:=Gamma0) |
  apply IHHT2 with (Gamma:=Gamma0) ]; 
eauto.
apply t_appl_LF with (A:=A);
[ skip |  (* ok_Bg *)
  apply IHHT1 with (Gamma:=Gamma0) |
  apply IHHT2 with (Gamma:=Gamma0) ]; 
eauto.
apply t_appl_LF with (A:=A);
[ skip |  (* ok_Bg *)
  eapply IHHT1 |
  eapply IHHT2 ]; 
eauto.
(* box *)
apply t_box_LF with (L:=\{w'} \u L);
[ skip | (* ok_Bg *)
  intros]; 
unfold open_ctx in *;
rewrite notin_union in H1; destruct H1;
rewrite notin_singleton in *;
rewrite <- subst_ctx_comm; auto;
eapply H; eauto;
permut_simpl; assumption.
apply t_box_LF with (L:=\{w0} \u L);
[ skip | (* ok_Bg *)
  intros]; 
unfold open_ctx in *;
rewrite notin_union in H1; destruct H1;
rewrite notin_singleton in *;
rewrite <- subst_ctx_comm; auto;
eapply H; eauto;
permut_simpl; assumption.
apply t_box_LF with (L:=\{w''} \u L);
[ skip | (* ok_Bg *)
  intros]; 
unfold open_ctx in *;
rewrite notin_union in H2; destruct H2;
rewrite notin_singleton in *;
rewrite <- subst_ctx_comm; auto;
eapply H with (G0:=G0 & (w0, Gamma0)) (Gamma':=Gamma') (Gamma'':=Gamma''); eauto;
permut_simpl; rew_app in *; assumption.
(* unbox *)
case_if; 
(* w0 = w' 
   G ~=~ G' & (w', ..)
   ok_Bg (w0, ..) G --> ok_Bg (w0,.. ) (G' & w' ,..)
   -->
   contradiction *)
[ skip |
  constructor];
[ skip | (* ok_Bg *)
  apply IHHT with (Gamma:=Gamma0); eauto].
 
case_if; constructor;
[ skip | (* ok_Bg *)
  apply IHHT with (Gamma:=Gamma0); eauto].

case_if; 
(* ok_Bg ((w'', Gamma0) :: G) & G ~=~ (G0 & (w', ..) & (w'', ..)) -> contradiction*)
[ skip | 
  constructor];
[ skip | (* ok_Bg *)
  eapply IHHT; eauto].
(* unbox_fetch *)
case_if.
(* G' ~=~ G & (w, Gamma)
   G' ~=~ G'0 & (w'0, Gamma'0) -->
   G'0 & (w'0, Gamma'0) ~= G & (w, Gamma) 
   w = w'0
   ok_Bg (w, Gamma) :: G -->
   G'0 = G && Gamma'0 = Gamma *)
assert (Gamma'0 = Gamma) by skip;
assert (G'0 = G) by skip;
inversion H1; subst;
constructor;
[ skip | (* ok_Bg *)
  apply IHHT; auto].
(* H: G & (w, Gamma) ~=~ G'
   H0: G' ~=~ G'0 & (w'0, Gamma'0) -->
   G'0 & (w'0, Gamma'0) ~= G & (w, Gamma) 
   H1: w <> w'0 -->
   exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT *)
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split by skip;
destruct Split as (GH, Split); destruct Split as (GT); subst.
apply t_unbox_fetch_LF with (G:=GH++GT) (Gamma:=Gamma); 
[ skip | (* ok_Bg *)
  eapply IHHT; eauto | ]; 
permut_simpl;
(* H + H0 --> G & (w, Gamma) ~=~ GH & (w, Gamma) ++ GT & (w'0, Gamma'0) --> 
   remove (w,Gamma) from both sides *)
skip.

case_if.
(* w = w0 --> ok_Bg w,.. :: G & (w0, .. ) --> contradiction *)
skip.
destruct (eq_var_dec w w'0).
(* w = w'0 follows that G = G'0 and Gamma = Gamma'0 *)
assert (Gamma'0 = Gamma) by skip;
assert (G'0 = G) by skip;
subst; constructor; [skip | ].
eapply IHHT with (w:=w'0) (Gamma1:=Gamma) (Gamma':=Gamma0); eauto.
(* w <> w'0
   H & H0 -> G'0 & (w'0, Gamma'0) ~=~ G & (w, Gamma) -->
   exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT *)
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split by skip;
destruct Split as (GH, Split); destruct Split as (GT); subst.
apply t_unbox_fetch_LF with (G:=GH++GT) (Gamma:=Gamma);
[ skip | (* ok_Bg *)
  eapply IHHT; eauto | ];
permut_simpl.
(* H + H0 --> G & (w, Gamma) ~=~ GH & (w, Gamma) ++ GT & (w'0, Gamma'0) --> 
   remove (w,Gamma) from both sides *)
skip.

case_if.
(* w = w'' 
   (G0 & (w'0, Gamma'0) & (w'', Gamma'')) ~=~ G & (w, Gamma) -->
   G0 & (w'0, Gamma'0) ~=~ G /\ Gamma'' = Gamma *)
inversion H2;
assert (permut G (G0 & (w'0, Gamma'0))) by skip;
assert (Gamma'' = Gamma) by skip;
subst.
apply t_unbox_fetch_LF with (G:=G0) (Gamma:=Gamma'0 ++ Gamma).
skip. (* ok_Bg *)
apply IHHT; eauto.
(* TODO: get rid of those 2 proofs, some permut_auto .. *)
permut_simpl; assumption.
apply permut_sym; assumption.
assert (w <> w0) by skip. (* from ok_Bg *)
destruct (eq_var_dec w w'0).
(* w = w'0 follows that G = G'0 and Gamma = Gamma'0 *)
assert (Gamma'0 = Gamma) by skip;
assert (G'0 = G) by skip;
subst. 
(* ok_Bg w'0, Gamma :: G & (w0, Gamma0)
   G ~=~ G0 & (w'0, Gamma ++ Gamma'') --->
   variables from Gamma will be doubled; they should be unique;
   contradiction *)
skip.
(* w <> w'0 /\ w <> w'
   H & H0 -> G0 & (w'0, Gamma'0) & (w'', Gamma'') ~=~ G & (w, Gamma) -->
   exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT *)
assert (exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT) as Split by skip;
destruct Split as (GH, Split); destruct Split as (GT); subst.
apply t_unbox_fetch_LF with (G:=GH++GT & (w'0, Gamma'0++Gamma'')) (Gamma:=Gamma).
skip.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (G0:=GH++GT & (w0,Gamma0)) (Gamma':=Gamma'0) (Gamma'':=Gamma''); eauto.
(* permut_auto desperately needed! *)
permut_simpl; skip. (* H + H1 + permutation magic *)
permut_simpl.
apply permut_sym.
apply permut_trans with (l2 := (GH & (w, Gamma) ++ GT) & (w'0, Gamma'0 ++ Gamma''));
[auto | permut_simpl].
(* here  -- same as unbox *)
case_if; 
(* w0 = w' 
   G ~=~ G' & (w', ..)
   ok_Bg (w0, ..) G --> ok_Bg (w0,.. ) (G' & w' ,..)
   -->
   contradiction *)
[ skip |
  constructor];
[ skip | (* ok_Bg *)
  apply IHHT with (Gamma:=Gamma0); eauto].
 
case_if; constructor;
[ skip | (* ok_Bg *)
  apply IHHT with (Gamma:=Gamma0); eauto].

case_if; 
(* ok_Bg ((w'', Gamma0) :: G) & G ~=~ (G0 & (w', ..) & (w'', ..)) -> contradiction*)
[ skip | 
  constructor];
[ skip | (* ok_Bg *)
  eapply IHHT; eauto].

(* get_here  -- same as unbox_fetch *)
case_if.
(* G' ~=~ G & (w, Gamma)
   G' ~=~ G'0 & (w', Gamma') -->
   G'0 & (w', Gamma') ~= G & (w, Gamma) 
   w = w'
   ok_Bg (w, Gamma) :: G -->
   G'0 = G && Gamma' = Gamma *)
assert (Gamma' = Gamma) by skip;
assert (G'0 = G) by skip;
inversion H2; subst;
constructor;
[ skip | (* ok_Bg *)
  apply IHHT; auto].
(* H: G & (w, Gamma) ~=~ G'
   H0: G' ~=~ G'0 & (w', Gamma') -->
   G'0 & (w', Gamma') ~= G & (w, Gamma) 
   H1: w <> w' -->
   exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT *)
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split by skip;
destruct Split as (GH, Split); destruct Split as (GT); subst.
apply t_get_here_LF with (G:=GH++GT) (Gamma:=Gamma); 
[ skip | (* ok_Bg *)
  eapply IHHT; eauto | ]; 
permut_simpl;
(* H + H0 --> G & (w, Gamma) ~=~ GH & (w, Gamma) ++ GT & (w'0, Gamma'0) --> 
   remove (w,Gamma) from both sides *)
skip.

case_if.
(* w = w0 --> ok_Bg w,.. :: G & (w0, .. ) --> contradiction *)
skip.
destruct (eq_var_dec w w').
(* w = w'0 follows that G = G'0 and Gamma = Gamma' *)
assert (Gamma' = Gamma) by skip;
assert (G'0 = G) by skip;
subst; constructor; [skip | ].
eapply IHHT with (w:=w') (Gamma1:=Gamma) (Gamma':=Gamma0); eauto.
(* w <> w'0
   H & H0 -> G'0 & (w'0, Gamma'0) ~=~ G & (w, Gamma) -->
   exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT *)
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split by skip;
destruct Split as (GH, Split); destruct Split as (GT); subst.
apply t_get_here_LF with (G:=GH++GT) (Gamma:=Gamma);
[ skip | (* ok_Bg *)
  eapply IHHT; eauto | ];
permut_simpl.
(* H + H0 --> G & (w, Gamma) ~=~ GH & (w, Gamma) ++ GT & (w'0, Gamma'0) --> 
   remove (w,Gamma) from both sides *)
skip.

case_if.
(* w = w'' 
   (G0 & (w'0, Gamma'0) & (w'', Gamma'')) ~=~ G & (w, Gamma) -->
   G0 & (w'0, Gamma'0) ~=~ G /\ Gamma'' = Gamma *)
inversion H3;
assert (permut G (G0 & (w', Gamma'))) by skip;
assert (Gamma'' = Gamma) by skip;
subst.
apply t_get_here_LF with (G:=G0) (Gamma:=Gamma' ++ Gamma).
skip. (* ok_Bg *)
apply IHHT; eauto.
(* TODO: get rid of those 2 proofs, some permut_auto .. *)
permut_simpl; assumption.
apply permut_sym; assumption.
assert (w <> w0) by skip. (* from ok_Bg *)
destruct (eq_var_dec w w').
(* w = w'0 follows that G = G'0 and Gamma = Gamma'0 *)
assert (Gamma' = Gamma) by skip;
assert (G'0 = G) by skip;
subst. 
(* ok_Bg w'0, Gamma :: G & (w0, Gamma0)
   G ~=~ G0 & (w'0, Gamma ++ Gamma'') --->
   variables from Gamma will be doubled; they should be unique;
   contradiction *)
skip.
(* w <> w'0 /\ w <> w'
   H & H0 -> G0 & (w'0, Gamma'0) & (w'', Gamma'') ~=~ G & (w, Gamma) -->
   exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT *)
assert (exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT) as Split by skip;
destruct Split as (GH, Split); destruct Split as (GT); subst.
apply t_get_here_LF with (G:=GH++GT & (w', Gamma'++Gamma'')) (Gamma:=Gamma).
skip.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (G0:=GH++GT & (w0,Gamma0)) (Gamma':=Gamma') (Gamma'':=Gamma''); eauto.
(* permut_auto desperately needed! *)
permut_simpl; skip. (* H + H1 + permutation magic *)
permut_simpl.
apply permut_sym.
apply permut_trans with (l2 := (GH & (w, Gamma) ++ GT) & (w', Gamma' ++ Gamma''));
[auto | permut_simpl].
(* letdia *)
case_if.
(* w0 = w' ->
   ok_Bg w', Gamma0 :: G' & (w', Gamma') ->
   contradiction *)
skip.
apply t_letdia_LF with (L_w:=L_w \u \{w'}) (L_t:=L_t) (A:=A).
skip. (* ok_Bg *)
eapply IHHT with (w:=w0) (Gamma:=Gamma0); eauto.
intros. 
rewrite notin_union in H3; destruct H3.
rewrite notin_singleton in H4.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (Gamma:=Gamma0) (w':=w'0); eauto.
permut_simpl; assumption.
simpl; auto.
intro; subst; elim H4; reflexivity.

case_if.
apply t_letdia_LF with (L_w:=L_w \u \{w0}) (L_t:=L_t) (A:=A).
skip. (* ok_Bg *)
eapply IHHT with (w:=w0) (Gamma:=Gamma0); eauto.
intros. 
rewrite notin_union in H3; destruct H3.
rewrite notin_singleton in H4.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (Gamma:=Gamma0) (w':=w'0); eauto.
permut_simpl; assumption.
simpl; auto.
intro; subst; elim H4; reflexivity.

case_if.
(* w0 = w'' -> H0 + Ok_Bg = contradiction *)
skip. 
apply t_letdia_LF with (L_w:=L_w \u \{w''}) (L_t:=L_t) (A:=A).
skip. (* ok_Bg *)
eapply IHHT with (w:=w0) (Gamma:=Gamma0); eauto.
intros. 
rewrite notin_union in H4; destruct H4.
rewrite notin_singleton in H5.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (Gamma:=Gamma0) (G0:=G0 & ((w'0, (v', A)::nil))); eauto.
permut_simpl; rew_app in *; eassumption.
permut_simpl; assumption.
simpl; auto.
intro; subst; elim H5; reflexivity.
(* letdia_get *)
case_if.
inversion H3; subst.
(* w = w' ->
   H1 + H0 = G & w', Gamma ~=~ G' & w', Gamma' ->
   Gamma = Gamma' /\ G = G' *)
assert (Gamma=Gamma') by skip;
assert (G = G') by skip;
subst.   
eapply t_letdia_LF with (L_w := L_w \u \{w'}).
skip. (* ok_Bg *)
eapply IHHT; eauto.
intros. 
rewrite notin_union in H5; destruct H5.
rewrite notin_singleton in H6.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (Gamma:=Gamma0); eauto.
simpl; auto.
intro; subst; elim H6; reflexivity.

destruct (eq_var_dec w w0).
subst; skip. (* ok_Bg -> contradiction *)
(* H0 + H1: G & (w, Gamma) ~=~ G' & (w', Gamma') -->
   exists GH, exists GT, G = GH & (w', Gamma') ++ GT *)
assert (exists GH, exists GT, G' = GH & (w, Gamma) ++ GT) by skip;
destruct H4 as (GH, H4); destruct H4 as (GT, H4).
apply t_letdia_get_LF with (L_w:=L_w \u \{w'}) (L_t:=L_t) (A:=A) (G:=GH++GT) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT with (w1:=w) (G0:=GH++GT) (w':=w0) (Gamma':=Gamma0) (Gamma'':=Gamma');
eauto.
subst; permut_simpl. skip. (* H0 + H1 *)
intros. 
rewrite notin_union in H6; destruct H6.
rewrite notin_singleton in H7.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w1:=w0) (Gamma1:=Gamma0); eauto.
permut_simpl. skip. (* H0 + H1 *)
simpl; auto.
intro; subst; elim H7; auto.
subst; permut_simpl.

case_if.
skip. (* w = w0 --> ok_Bg gives contradiction *)
destruct (eq_var_dec w w').
subst; skip. (* H0 + Ok_Bg gives contradiction *) 
(* H0 + H1: G & (w, Gamma) ~=~ G' & (w', Gamma') -->
   exists GH, exists GT, G = GH & (w', Gamma') ++ GT *)
assert (exists GH, exists GT, G' = GH & (w, Gamma) ++ GT) by skip;
destruct H4 as (GH, H4); destruct H4 as (GT, H4).
apply t_letdia_get_LF with (L_w:=L_w \u \{w0}) (L_t:=L_t) (A:=A) (G:=GH++GT) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT; eauto.
subst; permut_simpl. skip. (* H0 + H1 *)
intros. 
rewrite notin_union in H6; destruct H6.
rewrite notin_singleton in H7.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w1:=w0) (Gamma1:=Gamma0); eauto.
permut_simpl. skip. (* H0 + H1 + H4 *)
simpl; auto.
intro; subst; elim H7; auto.
subst; permut_simpl.

case_if.
inversion H4; subst.
(* H0 + H1 + Ok_Bg --> Gamma'' = Gamma & G0 & (w', Gamma') ~=~ G *)
assert (Gamma'' = Gamma) by skip.
assert (G1 & (w', Gamma') = G) by skip.
subst.
eapply t_letdia_get_LF with (G:=G1) (Gamma:=Gamma'++Gamma) (L_w:=L_w \u \{w''}).
skip.
eapply IHHT; eauto. 
permut_simpl.
intros. 
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (G0:=(w'0, (v',A)::nil)::G1); eauto. 
permut_simpl.
permut_simpl.
simpl; auto.
rewrite notin_union in H6; 
rewrite notin_singleton in H6;
destruct H6; intro; elim H7; auto.
apply permut_sym; auto.

destruct (eq_var_dec w w').
subst.
(* H0 + H1 + Ok_Bg --> Gamma = Gamma' /\ G0 & (w'',Gamma'') = G *)
assert (Gamma' = Gamma) by skip.
assert (G1 & (w'', Gamma'') = G) by skip.
subst.
eapply t_letdia_get_LF with (G:=G1) (Gamma:=Gamma++Gamma'') (L_w:=L_w \u \{w''}).
skip.
eapply IHHT with (w:=w'); eauto. 
permut_simpl.
intros. 
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (G0:=(w'0, (v',A)::nil)::G1) (Gamma':=Gamma); eauto. 
permut_simpl.
permut_simpl.
simpl; auto.
rewrite notin_union in H6; 
rewrite notin_singleton in H6;
destruct H6; intro; elim H7; auto.
apply permut_sym; auto.
(* H0 + H1: G & (w, Gamma) ~=~ G1 & (w', Gamma') & (w'', Gamma'') -->
   exists GH, exists GT, G1 = GH & (w, Gamma) & (w', Gamma') ++ GT *)
assert (exists GH, exists GT, G1 = GH & (w, Gamma) ++ GT) by skip;
destruct H5 as (GH, H5); destruct H5 as (GT, H5); subst.
apply t_letdia_get_LF with (L_w:=L_w \u \{w''}) 
  (L_t:=L_t) (A:=A) (G:=GH++GT & (w', Gamma'++Gamma'')) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT with (w1:=w) (G0:=GH++GT & (w0, Gamma0)) (Gamma':=Gamma') (Gamma'':=Gamma''); eauto.
subst; permut_simpl. skip. (* H0 + H1 *)
permut_simpl.
intros. 
rewrite notin_union in H6; destruct H6.
rewrite notin_singleton in H7.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (G0:=(w'0, (v', A) :: nil) :: (GH ++ GT) & (w, Gamma)); eauto.
permut_simpl. skip. (* H0 + H1 *)
permut_simpl.
simpl; auto.
intro; subst; elim H7; auto.
subst; permut_simpl.
apply permut_sym. 
skip. (*trans with H2 *)
Admitted. (* "No more subgoals but non-instantiated existential variables" *)

Lemma rename_w_preserv_types_new:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG': permut G (G' & (w', Gamma'))),
  G' |= (w, Gamma ++ Gamma') |- {{ fctx w // fctx w' }} M ::: A.
intros;
apply rename_w_preserv_types with (G := G) (w := w) (w':= w'); eauto.
Qed.

Lemma rename_w_preserv_types_old:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG': permut G (G' & (w', Gamma'))),
  G' |= (w', Gamma' ++ Gamma) |- {{ fctx w' // fctx w }} M ::: A.
intros;
apply rename_w_preserv_types with (G := G) (w := w) (w':= w'); eauto.
Qed.

Lemma rename_w_preserv_types_outer:
forall G G0 w Gamma A M G' w' Gamma' w'' Gamma''
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG: permut G (G0 & (w', Gamma') & (w'', Gamma'')))
  (GG': permut G' (G0 & (w', Gamma' ++ Gamma''))),
  G' |= (w, Gamma) |- {{ fctx w' // fctx w'' }} M ::: A.
intros;
eapply rename_w_preserv_types;
eauto.
Qed.

Lemma Progress:
forall G w M A
  (H_lc_w: lc_w_LF M)
  (H_lc_t: lc_t_LF M)
  (HT: emptyEquiv G |= (w, nil) |- M ::: A),
  value_LF M \/ exists N, (M, fctx w) |-> (N, fctx w).
intros;
remember (w, (@nil ty_LF)) as Ctx;
generalize dependent Ctx;
generalize dependent A;
generalize dependent w;
generalize dependent G.
induction M; intros; eauto using value_LF;
inversion HeqCtx; subst.
(* hyp *)
inversion HT; subst;
rewrite Mem_nil_eq in HT0;
contradiction.
(* appl *)
right; inversion HT; subst;
inversion H_lc_t; subst;
inversion H_lc_w; subst;
edestruct IHM1 with (A := A0 ---> A); eauto;
[ inversion H0; subst; inversion HT1; subst | 
  destruct H0];
eexists; constructor; eauto;
inversion H2; inversion H3; subst; eauto.
(* unbox & unbox_fetch *)
right; inversion HT; subst;
inversion H_lc_w; subst;
inversion H_lc_t; subst.
(* unbox *)
edestruct IHM with (A := [*]A); eauto;
[ inversion H0; subst; inversion HT0; subst |
  destruct H0];
eexists; constructor; eauto;
inversion H3; inversion H4; subst; auto.
(* unbox_fetch *)
(* TODO: permut (G0 & (w0, Gamma)) (emptyEquiv G) --> Gamma = nil *)
assert (Gamma = nil) by skip; subst. 
destruct IHM with (A := [*]A) 
                  (Ctx := (w0, (@nil ty_LF)))
                  (G := G0 & (w0, nil))
                  (w := w0); 
eauto;
(* TODO: emptyEqiv (G0 & (w0, nil)) = G0 & (w0, nil) by H6 *) 
[ skip |
  inversion H0; subst; inversion HT0; subst | 
  destruct H0 ];
eexists; constructor; eauto;
inversion H3; inversion H4; subst; 
eauto.
(* here & get_here *)
inversion HT; subst;
inversion H_lc_w; subst;
inversion H_lc_t; subst.
(* here *)
edestruct IHM; eauto;
[ left; econstructor|
  right; destruct H0; eexists];
eauto using step_LF.
(* get_here *)
(* TODO: permut (G0 & (w0, Gamma)) (emptyEquiv G) --> Gamma = nil *)
assert (Gamma = nil) by skip; subst;
edestruct IHM with (A := A0) (G := G0 & (w0, nil)) (w:=w0); eauto;
(* TODO: emptyEqiv (G0 & (w0, nil)) = G0 & (w0, nil) by H5 *) 
[ skip | 
  left; inversion H0; subst; inversion HT0; subst | 
  right; destruct H0; eexists];
econstructor; eauto using step_LF.
(* letdia & letdia_get *)
right; inversion HT; subst;
inversion H_lc_w; subst;
inversion H_lc_t; subst.
(* letdia *)
edestruct IHM1 with (A := <*>A0); eauto;
[ inversion H0; subst; inversion HT1; subst |
  destruct H0];
eexists; constructor; eauto;
try apply closed_t_succ; auto;
inversion H5; inversion H7; subst; auto.
(* letdia_get *)
(* TODO: permut (G0 & (w0, Gamma)) (emptyEquiv G) --> Gamma = nil *)
assert (Gamma = nil) by skip; subst.
edestruct IHM1 with (G := G0 & (w, nil)) 
                    (w := w0) 
                    (Ctx := (w0, (@nil ty_LF)))
                    (A := <*>A0); eauto;
(* TODO: emptyEqiv (G0 & (w0, nil)) = G0 & (w0, nil) by H6 *) 
[ skip |
  inversion H0; subst; inversion HT1; subst |
  destruct H0];
eexists; constructor; eauto;
try apply closed_t_succ; auto;
inversion H5; inversion H8; subst; auto.
Qed.


Lemma Preservation:
forall G M N A w
  (HT: emptyEquiv G |= (w, nil) |- M ::: A)
  (HS: (M, fctx w) |-> (N, fctx w)),
  emptyEquiv G |= (w, nil) |- N ::: A.
intros;
remember (w, (@nil (var * ty_LF))) as Ctx;
remember (emptyEquiv G) as G';
generalize dependent w;
generalize dependent N;
generalize dependent G;
induction HT; intros;
inversion HS; subst;
try (inversion HeqCtx; subst);
eauto using types_LF.
(* appl_lam *)
inversion HT1; subst;
unfold open_var in *;
assert (exists v, v \notin L) as HF by apply Fresh;
destruct HF as (v_fresh).
replace ( [N // bvar 0]M0 ) with ( [N // fvar v_fresh] [hyp_LF (fvar v_fresh) // bvar 0] M0 ) by skip. (* ! TODO ! *)
eapply subst_t_preserv_types_inner; eauto.
(* TODO: Double emptyEquiv doesn't change more than single *)
skip.
(* unbox_box *)
inversion HT; subst;
assert (exists v, v \notin L \u (free_worlds_LF M0)) as HF by apply Fresh;
destruct HF as (w_fresh);
unfold open_ctx in *;
replace ({{fctx w0 // bctx 0}}M0)
  with ({{fctx w0 // fctx w_fresh}} {{fctx w_fresh // bctx 0}}M0)
  by (rewrite subst_ctx_neutral_free; auto);
replace (@nil (var * ty_LF)) with (nil ++ (@nil (var * ty_LF))); eauto;
apply rename_w_preserv_types_old with (G := emptyEquiv G0 & (w0, nil));
eauto.
(* unbox_fetch_box *)
inversion HT; subst;
assert (exists v, v \notin L \u (free_worlds_LF M0)) as HF by apply Fresh;
destruct HF as (w_fresh);
unfold open_ctx in *;
replace ({{fctx w0 // bctx 0}}M0)
  with ({{fctx w0 // fctx w_fresh}} {{fctx w_fresh // bctx 0}}M0)
  by (rewrite subst_ctx_neutral_free; auto);
replace (@nil (var * ty_LF)) with (nil ++ (@nil (var * ty_LF))); eauto;
apply rename_w_preserv_types_old with (G := G & (w0, nil) & (w, Gamma));
try permut_simpl;
eauto.
(* unbox_fetch *)
econstructor; eauto;
(* TODO: permut (G & (w, Gamma)) (emptyEquiv G0) -> Gamma = nil *)
assert (Gamma = nil) by skip; subst;
eapply IHHT with (G0:=G & (w0, nil)); eauto;
(* TODO: by H, G contains no Gammas <> nil, so taking emptyEquiv doesn't change anything *)
skip.
(* get_here *)
econstructor; eauto;
(* TODO: permut (G & (w, Gamma)) (emptyEquiv G0) -> Gamma = nil *)
assert (Gamma = nil) by skip; subst;
eapply IHHT with (G0:=G & (w0, nil)); eauto;
(* TODO: by H, G contains no Gammas <> nil, so taking emptyEquiv doesn't change anything *)
skip.
(* letdia + (here | get_here ) *)
assert (exists w1, w1 \notin L_w \u free_worlds_LF N) as HF by apply Fresh;
assert (exists v1, v1 \notin L_w) as HF2 by apply Fresh;
destruct HF as (w_fresh); destruct HF2 as (v_fresh);
inversion HT; subst. 
(* letdia here *)
apply subst_t_preserv_types_inner with (L:=L_t) (A:=A); auto.
intros.
unfold open_ctx in *; unfold open_var in *.
rewrite <- subst_ctx_neutral_free with (w0:=w_fresh);
eauto; rewrite <- subst_ctx_neutral_bound with (n:=0).
eapply rename_w_preserv_types_new.
[ | skip ]. (* emptyEquiv (emptyEquiv G) = emptyEquiv G + HT0 *)
intros. apply 

skip.
skip.
Qed.

End Lemmas.

Close Scope label_free_is5_scope.
