Add LoadPath "../..".
Require Import LFND_OkLib.
Require Import LFND_EmptyEquivLib.
Require Import LFND_Substitution.
Require Import LFND_Syntax.

Open Scope permut_scope.
Open Scope is5_scope.

Reserved Notation " G  '|=' Gamma '|-' M ':::' A" (at level 70).

Inductive types_LF : bg_LF -> ctx_LF -> te_LF -> ty -> Type :=

| t_hyp_LF: forall A G Gamma v
  (Ok: ok_Bg_LF (Gamma::G))
  (H: Mem (v, A) Gamma),
  G |= Gamma |- hyp_LF (fte v) ::: A

| t_lam_LF: forall L A B G Gamma M
  (Ok: ok_Bg_LF (Gamma::G))
  (H: forall v, v \notin L ->
    G |= (v, A)::Gamma |- M ^t^ (hyp_LF (fte v)) ::: B),
  G |= Gamma |- lam_LF A M ::: A ---> B

| t_appl_LF: forall A B G Gamma M N
  (Ok: ok_Bg_LF (Gamma::G))
  (H1: G |= Gamma |- M ::: A ---> B)
  (H2: G |= Gamma |- N ::: A),
  G |= Gamma |- appl_LF M N ::: B

| t_box_LF: forall G Gamma M A
  (Ok: ok_Bg_LF (G & Gamma))
  (H: G & Gamma |= nil |- M ::: A),
  G |= Gamma |- box_LF M ::: [*] A

| t_unbox_LF: forall G Gamma M A
  (Ok: ok_Bg_LF (Gamma :: G))
  (H: G |= Gamma |- M ::: [*] A),
  G |= Gamma |- unbox_LF M ::: A

| t_unbox_fetch_LF: forall G Gamma Gamma' M A
  (Ok: ok_Bg_LF (Gamma:: G & Gamma'))
  (H: G & Gamma' |= Gamma |- M ::: [*] A),
  forall G', G & Gamma ~=~ G' ->
    G' |= Gamma' |- unbox_LF M ::: A

where " G '|=' Gamma '|-' M ':::' A" := (types_LF G Gamma M A).

Inductive value_LF: te_LF -> Type :=
| val_lam_LF: forall A M, value_LF (lam_LF A M)
| val_box_LF: forall M, value_LF (box_LF M)
.

Reserved Notation " M |-> N " (at level 70).

Inductive step_LF: te_LF -> te_LF -> Type :=

| red_appl_lam_LF: forall M N A,
  lc_t_n_LF 1 M -> lc_t_LF N ->
  appl_LF (lam_LF A M) N |-> [N // bte 0] M

| red_unbox_box_LF: forall M,
  lc_t_LF M ->
  unbox_LF (box_LF M)|-> M

| red_appl_LF: forall M M' N,
  lc_t_LF M -> lc_t_LF N ->
  M |-> M'->
  appl_LF M N |-> appl_LF M' N

| red_unbox_LF: forall M M',
  lc_t_LF M -> M |-> M' ->
  unbox_LF M |-> unbox_LF M'

where " M |-> N " := (step_LF M N ).

Inductive steps_LF : te_LF -> te_LF -> Type :=
| single_step_LF: forall M M', M |-> M' -> steps_LF M M'
| multi_step_LF: forall M M' M'',
  M |-> M' -> steps_LF M' M'' -> steps_LF M M''
.

Lemma PPermutationG_LF:
forall G Gamma M A G',
  G |= Gamma |- M ::: A ->
  G ~=~ G' ->
  G' |= Gamma |- M ::: A.
intros; generalize dependent G'; induction X; intros; simpl in *.

constructor; [apply ok_Bg_LF_PPermut with (G:=Gamma::G)| ]; auto;
PPermut_LF_simpl.

apply t_lam_LF with (L:=L);
[apply ok_Bg_LF_PPermut with (G:=Gamma::G)| ]; auto; PPermut_LF_simpl.

apply t_appl_LF with (A:=A);
[apply ok_Bg_LF_PPermut with (G:=Gamma::G)| |]; auto; PPermut_LF_simpl.

constructor;
[apply ok_Bg_LF_PPermut with (G:=G & Gamma)|]; auto.

constructor;
[apply ok_Bg_LF_PPermut with (G:=Gamma::G)|]; auto.

apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto.
transitivityP G'; auto.
Qed.

Lemma PermutationGamma_LF:
forall G Gamma M A Gamma',
  G |= Gamma |- M ::: A ->
  Gamma *=* Gamma' ->
  G |= Gamma' |- M ::: A.
intros. generalize dependent Gamma'.
induction X; intros; simpl in *.

constructor;
[apply ok_Bg_LF_PPermut with (G:=Gamma::G) |
 apply Mem_permut with (l:=Gamma)]; auto.

apply t_lam_LF with (L:=L);
[apply ok_Bg_LF_PPermut with (G:=Gamma::G) |]; auto.

apply t_appl_LF with (A:=A);
[apply ok_Bg_LF_PPermut with (G:=Gamma::G) | |]; auto.

constructor;
[apply ok_Bg_LF_PPermut with (G:=G & Gamma) |]; auto.
apply PPermutationG_LF with (G:=G & Gamma);
auto.

constructor;
[apply ok_Bg_LF_PPermut with (G:= Gamma :: G) |]; auto.

apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma);
[apply ok_Bg_LF_PPermut with (G:= Gamma :: G & Gamma') | |]; auto.
apply PPermutationG_LF with (G:=G & Gamma'); auto.
Qed.

Lemma WeakeningG_LF:
forall G Gamma M A Delta,
  G |= Gamma |- M ::: A ->
  ok_Bg_LF (Gamma::Delta::G) ->
  Delta :: G |= Gamma |- M ::: A.
intros; generalize dependent Delta; induction X;
intros; simpl in *; eauto using types_LF.

apply t_lam_LF with (L:=L \u used_vars_ctx_LF (Gamma:: Delta :: G));
auto; intros;
apply X; auto; apply ok_Bg_LF_fresh; auto;
apply notin_Mem; rewrite notin_union in H2; destruct H2; auto.

constructor;
[apply ok_Bg_LF_PPermut with (G:=Gamma::Delta::G) | rew_app ];
auto. rew_app; PPermut_LF_simpl. apply IHX; apply ok_Bg_LF_nil;
apply ok_Bg_LF_PPermut with (G:=Gamma::Delta::G); auto. PPermut_LF_simpl.

apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=Delta :: G);
[apply ok_Bg_LF_PPermut with (G:=Gamma'::Delta::G') | |]; auto;
rew_app. transitivityP (Gamma'::Delta::G & Gamma); auto; PPermut_LF_simpl.
apply IHX; eapply ok_Bg_LF_PPermut; eauto.
transitivityP (Gamma'::Delta::G & Gamma); auto; PPermut_LF_simpl.
transitivityP (Delta::G & Gamma); auto.
Qed.

Lemma WeakeningWithinContext_LF:
forall G Gamma M A,
  G |= Gamma |- M ::: A ->
  (forall Delta Delta' G',
    G' & Delta ~=~ G ->
    ok_Bg_LF (Gamma :: G' & (Delta ++ Delta')) ->
    G' & (Delta++Delta') |= Gamma |- M ::: A) *
  (forall Gamma',
    ok_Bg_LF ((Gamma++Gamma')::G) ->
    G |= Gamma ++ Gamma' |- M ::: A).
intros G Gamma M A H;
induction H; split; intros; subst.
constructor; auto.
constructor; auto; rewrite Mem_app_or_eq; left; auto.
apply t_lam_LF with
  (L:=L \u
    (used_vars_ctx_LF (Gamma :: G' & (Delta ++ Delta'))));
auto; intros; eapply X; eauto;
rew_app; apply ok_Bg_LF_fresh; eauto; apply notin_Mem;
rewrite notin_union in H3; destruct H3; auto.
apply t_lam_LF with
  (L:=L \u
    (used_vars_ctx_LF ((Gamma ++ Gamma') :: G)));
auto; intros; eapply X; eauto;
rew_app; apply ok_Bg_LF_fresh; eauto;
rewrite notin_union in H1; destruct H1; auto.
econstructor; eauto; [eapply IHtypes_LF1 | eapply IHtypes_LF2]; eauto.
econstructor; eauto; [eapply IHtypes_LF1 | eapply IHtypes_LF2]; eauto.
econstructor;
[apply ok_Bg_LF_PPermut with (G:=Gamma:: G' & (Delta++Delta')) | ];
auto. PPermut_LF_simpl.
apply PPermutationG_LF with (G:= ((G'& Gamma) & (Delta ++ Delta'))).
eapply IHtypes_LF. transitivityP (G' & Delta & Gamma); auto; PPermut_LF_simpl.
apply ok_Bg_LF_nil; apply ok_Bg_LF_PPermut
  with (G:=Gamma :: G' & (Delta ++ Delta'));
auto. PPermut_LF_simpl.
econstructor;
[apply ok_Bg_LF_PPermut with (G:=(Gamma++Gamma'):: G) | ];
auto. PPermut_LF_simpl.
eapply IHtypes_LF; auto.
apply ok_Bg_LF_nil; apply ok_Bg_LF_PPermut with (G:=(Gamma++Gamma') :: G);
auto. PPermut_LF_simpl.
constructor; eauto; eapply IHtypes_LF; eauto.
constructor; eauto; eapply IHtypes_LF; eauto.
assert (Delta::G'0 ~=~ G & Gamma).
  transitivityP G'; auto; transitivityP (G'0 & Delta); auto; PPermut_LF_simpl.
assert ({Gamma *=* Delta} + {~ Gamma *=* Delta}).
  eapply permut_dec; intros; destruct k; destruct k'; repeat decide equality.
  apply eq_var_dec.
destruct H3.
(* Gamma *=* Delta *)
assert (G'0 ~=~ G).
  apply PPermut_LF_last_rev with (Gamma:=Delta) (Gamma':=Gamma).
  symmetry; auto. transitivityP (Delta::G'0); auto; PPermut_LF_simpl.
apply t_unbox_fetch_LF with (G:=G'0) (Gamma:=Delta++Delta'); auto.
apply ok_Bg_LF_PPermut with (G:=Gamma'::G'0&(Delta++Delta')); auto.
apply PPermutationG_LF with (G:=G & Gamma'); auto.
apply PermutationGamma_LF with (Gamma:=Gamma++Delta'); auto.
eapply IHtypes_LF.
apply ok_Bg_LF_PPermut with (G:=Gamma'::G'0&(Delta++Delta')); auto.
transitivityP ((Gamma++Delta') :: G'0 & Gamma'); auto; PPermut_LF_simpl.
(* ~ Gamma *=* Delta *)
assert (G'0 & Delta ~=~ G & Gamma).
transitivityP (Delta::G'0); auto; PPermut_LF_simpl.
apply PPermut_LF_split_neq_T in H3; [ | intro; elim n; symmetry; auto].
destruct H3 as (t, (H4, H5)). destruct t as (t', tl);
destruct t' as (Gamma0, hd); simpl in *; subst.
apply t_unbox_fetch_LF with (G:=hd++tl & (Delta++Delta')) (Gamma:=Gamma).
apply ok_Bg_LF_PPermut
  with (G:=Gamma' :: (hd & Gamma0 ++ tl) & (Delta ++ Delta'));
auto; rew_app; PPermut_LF_simpl.
apply PPermutationG_LF with (G:=(hd& Gamma' ++ tl) & (Delta ++ Delta')).
eapply IHtypes_LF. rew_app; PPermut_LF_simpl.
apply PPermut_LF_last_rev with (Gamma:=Gamma0) (Gamma':=Gamma); auto.
transitivityP (Delta :: hd & Gamma0 ++ tl); auto; PPermut_LF_simpl.
apply ok_Bg_LF_PPermut
  with (G:=Gamma' :: (hd & Gamma0 ++ tl) & (Delta ++ Delta'));
auto; rew_app; PPermut_LF_simpl.
rew_app; PPermut_LF_simpl.
rew_app; PPermut_LF_simpl.
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma);
[apply ok_Bg_LF_PPermut with (G:=(Gamma'++Gamma'0):: G') | | ];
auto. transitivityP ((Gamma'++Gamma'0) :: G & Gamma); auto; PPermut_LF_simpl.
eapply IHtypes_LF; auto.
apply ok_Bg_LF_PPermut with (G:=(Gamma'++Gamma'0):: G'); auto.
transitivityP ((Gamma' ++ Gamma'0) ::G & Gamma); auto.
Qed.

Lemma WeakeningGamma_LF:
forall G Gamma M A Gamma',
  G |= Gamma |- M ::: A ->
  ok_Bg_LF ((Gamma++Gamma')::G) ->
  G |= Gamma ++ Gamma' |- M ::: A.
intros; eapply WeakeningWithinContext_LF; eauto.
Qed.

Lemma WeakeningWithinG:
forall G Gamma M A Delta Delta',
  G & Delta |= Gamma |- M ::: A ->
  ok_Bg_LF (Gamma :: G & (Delta ++ Delta')) ->
  G & (Delta++Delta')|= Gamma |- M ::: A.
intros; eapply WeakeningWithinContext_LF; eauto.
Qed.

Lemma types_weakened_LF:
forall G G' Gamma M A
  (Ok: ok_Bg_LF (Gamma::G ++ G'))
  (HT: emptyEquiv_LF G ++ G' |= nil |- M ::: A),
  G ++ G'|= Gamma |- M ::: A.
induction G; intros; simpl in *; rew_app in *; auto.
apply WeakeningGamma_LF with (Gamma':=Gamma) in HT; rew_app in *; auto.
assert (a :: G ++ G' ~=~ G ++ a::G') by PPermut_LF_simpl.
apply PPermutationG_LF with (G:=G ++ a:: G'); auto; apply IHG.
apply ok_Bg_LF_PPermut with (G:=Gamma :: a :: G ++ G'); auto.
assert (emptyEquiv_LF G ++ a :: G' ~=~
  (emptyEquiv_LF G ++ G') & (nil ++ a)).
  PPermut_LF_simpl.
apply PPermutationG_LF with (G:=(emptyEquiv_LF G  ++ G') & (nil ++ a)); auto.
eapply WeakeningWithinG.
rew_app.
apply ok_Bg_LF_empty_first in Ok.
assert (nil :: a :: G ++ G' ~=~ (nil :: G) ++ a :: G') by
  PPermut_LF_simpl.
apply ok_Bg_LF_PPermut with (G':=(nil::G)++ a::G') in Ok; auto.
eapply emptyEquiv_LF_ok_Bg_part in Ok; simpl in *; rew_app in *; auto.
assert (emptyEquiv_LF G & nil ++ G' ~=~  nil :: emptyEquiv_LF G ++ G') by
  PPermut_LF_simpl.
apply PPermutationG_LF with (G:= nil::emptyEquiv_LF G ++ G'); auto.
PPermut_LF_simpl.
apply ok_Bg_LF_nil. rew_app. apply emptyEquiv_LF_ok_Bg_part.
apply ok_Bg_LF_PPermut with (a::G ++ G');
try PPermut_LF_simpl.
eapply ok_Bg_LF_weakening; eauto.
Qed.

Lemma subst_t_LF_preserv_types:
forall G Gamma B M N v A
  (H_lc_t: lc_t_LF M)
  (HT: G |= Gamma |- N ::: B),
  (* "inner" substitution *)
  ( forall Gamma0,
    Gamma *=* ((v, A) :: Gamma0) ->
    emptyEquiv_LF G |= nil |- M ::: A ->
    G |= Gamma0 |- [M // fte v] N ::: B)
  *
  (* "outer" substitution *)
  ( forall G0 G' G'' Gamma',
    G ~=~ (G0 & ((v,A)::Gamma')) ->
    G' ~=~ (G0 & Gamma) ->
    G'' ~=~ (G0 & Gamma') ->
    emptyEquiv_LF G' |= nil |- M ::: A ->
    G'' |= Gamma |- [M // fte v] N ::: B).
intros.
generalize dependent v;
generalize dependent A;
generalize dependent M.
induction HT; split; intros;
simpl in *.

(* hyp *)
case_if.
inversion H1; subst.
assert (A = A0) by (eapply ok_Bg_LF_Mem_eq; eauto);
subst; replace G with (G ++ nil) by (rew_app; auto).
apply types_weakened_LF.
apply ok_Bg_LF_permut_first_tail with (C':=Gamma0)(x:=v)(A:=A0) in Ok;
auto; rew_app; auto. rew_app; auto.

constructor.
apply ok_Bg_LF_permut_first_tail with (C':=Gamma0) (x:=v0) (A:=A0) in Ok; eauto.
apply Mem_permut with (l' := (v0, A0) :: Gamma0) in H; eauto;
rewrite Mem_cons_eq in H; destruct H; auto.
inversion H; subst; elim H1; reflexivity.


case_if.
inversion H3; subst.
apply ok_Bg_LF_Mem_contradict with (v:=v) (A:=A) (A':=A0) (G':=G0) (C':=Gamma')
  in Ok; rew_app in *;
contradiction || eauto.
constructor; auto.
apply ok_Bg_LF_PPermut with (G:=(Gamma::G0) & Gamma').
apply ok_Bg_LF_PPermut with (G':=(Gamma::G0 & ((v0, A0)::Gamma'))) in Ok.
apply ok_Bg_LF_permut_no_last with (v:=v0)(A:=A0); auto.
transitivityP (Gamma::G0 & ((v0, A0) :: Gamma')); auto; PPermut_LF_simpl.
transitivityP (Gamma::G0 & Gamma'); auto; PPermut_LF_simpl.

(* lam *)
apply t_lam_LF with (L:=L \u \{v}).
apply ok_Bg_LF_permut_first_tail with (C:=Gamma) (x:=v) (A:=A0); auto.
intros.
rewrite notin_union in H1; rewrite notin_singleton in H1; destruct H1.
unfold open_LF in *;
rewrite <- subst_t_comm_LF; auto.
eapply X; auto;
permut_simpl || rew_app; eauto.

apply t_lam_LF with (L:=L \u \{v}).
apply ok_Bg_LF_PPermut with (G':=Gamma::G0 & ((v,A0)::Gamma')) in Ok.
apply ok_Bg_LF_PPermut with (G:=(Gamma::G0) & Gamma').
apply ok_Bg_LF_permut_no_last with (v:=v) (A:=A0); rew_app; auto.
transitivityP (Gamma::G0 & Gamma'); auto.
transitivityP (Gamma :: G0 & ((v, A0) :: Gamma')); auto.
intros.
rewrite notin_union in H3; rewrite notin_singleton in H3; destruct H3;
unfold open_LF in *;
rewrite <- subst_t_comm_LF; auto.
eapply X with (G0:=G0); eauto;
assert (emptyEquiv_LF G' ~=~
  emptyEquiv_LF (G0 ++ nil & ((v0, A) :: Gamma))).
transitivityP (emptyEquiv_LF(G0 & Gamma)).
  apply PPermut_emptyEquiv_LF; auto.
rew_app; eapply emptyEquiv_LF_last_change; auto.
rew_app in *.
apply PPermutationG_LF with (G:=emptyEquiv_LF G'); auto.

(* appl *)
econstructor;  [ | eapply IHHT1 | eapply IHHT2]; eauto.
apply ok_Bg_LF_permut_first_tail with (C':=Gamma0) (x:=v) (A:=A0) in Ok; eauto.

econstructor.
apply ok_Bg_LF_PPermut with (G:=Gamma:: G0 & Gamma'); auto.
apply ok_Bg_LF_PPermut with (G':=Gamma :: G0 & ((v,A0)::Gamma')) in Ok; auto.

apply ok_Bg_LF_permut_no_last_spec in Ok; rew_app; auto.
eapply IHHT1; eauto.
eapply IHHT2; eauto.

(* box *)
constructor.
apply ok_Bg_LF_permut_no_last with (v:=v) (A:=A0);
apply ok_Bg_LF_PPermut with (G:=G & Gamma); auto.
eapply IHHT; eauto.
rewrite emptyEquiv_LF_rewrite; rewrite emptyEquiv_LF_rewrite_last;
simpl; rew_app. apply PPermutationG_LF with (nil :: emptyEquiv_LF G).
apply WeakeningG_LF; auto.

repeat apply ok_Bg_LF_nil. apply ok_Bg_LF_emptyEquiv.
PPermut_LF_simpl.

constructor.

apply ok_Bg_LF_PPermut with (G:=G0 & Gamma & Gamma').
apply ok_Bg_LF_permut_no_last with (v:=v) (A:=A0).
apply ok_Bg_LF_PPermut with (G:=G & Gamma); auto.
transitivityP (G0 & ((v, A0) :: Gamma') & Gamma); auto; PPermut_LF_simpl.
transitivityP (G0 & Gamma' & Gamma); auto; PPermut_LF_simpl.
eapply IHHT with (G0:=G0 & Gamma) (Gamma':=Gamma'); auto.
transitivityP (G0 & ((v, A0) :: Gamma') & Gamma); auto; PPermut_LF_simpl.
transitivityP (G0 & Gamma' & Gamma); auto; PPermut_LF_simpl.
repeat rewrite emptyEquiv_LF_rewrite;
simpl; rew_app.
apply PPermutationG_LF with (G:=nil::emptyEquiv_LF G').
apply WeakeningG_LF; auto.
repeat apply ok_Bg_LF_nil; apply ok_Bg_LF_emptyEquiv.
transitivityP (nil :: (emptyEquiv_LF(G0 & Gamma))).
  PPermut_LF_simpl. apply PPermut_emptyEquiv_LF. auto.
rewrite emptyEquiv_LF_rewrite_last; simpl;
PPermut_LF_simpl.

(* unbox *)
econstructor; [ | eapply IHHT]; eauto;
apply ok_Bg_LF_permut_first_tail with (C':=Gamma0) (x:=v) (A:=A0) in Ok; eauto.

econstructor.
apply ok_Bg_LF_PPermut with (G:=G0 & Gamma & Gamma').
apply ok_Bg_LF_permut_no_last with (v:=v) (A:=A0).
apply ok_Bg_LF_PPermut with (G:=Gamma :: G); auto.
transitivityP (Gamma::G0 & ((v, A0) :: Gamma')); auto; PPermut_LF_simpl.
transitivityP (Gamma :: G0 & Gamma'); auto; PPermut_LF_simpl.
eapply IHHT; eauto.

(* unbox_fetch *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto;
[ apply ok_Bg_LF_permut_no_last_spec with (v:=v) (A:=A0);
  apply ok_Bg_LF_PPermut with (G:= Gamma :: G & Gamma') |
  eapply IHHT; eauto]; auto.
rewrite emptyEquiv_LF_rewrite; simpl.
apply PPermutationG_LF with (emptyEquiv_LF G'); auto.
transitivityP (emptyEquiv_LF (G & Gamma)).
  apply PPermut_emptyEquiv_LF; auto.
  rewrite emptyEquiv_LF_rewrite; simpl; auto.

destruct (permut_dec (var * ty) Gamma ((v,A0)::Gamma'0)).
  intros; destruct k; destruct k'; repeat decide equality.
  apply eq_var_dec.
(* = *)
assert (G ~=~ G0).
  apply PPermut_LF_last_rev with (Gamma:=Gamma)(Gamma':=(v,A0)::Gamma'0);
  auto.
  transitivityP G'; auto.
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma'0).
apply ok_Bg_LF_PPermut with (Gamma' :: G & Gamma'0).
apply ok_Bg_LF_permut_no_last_spec with (v:=v)(A:=A0).
apply ok_Bg_LF_PPermut with (Gamma :: G & Gamma').
auto. transitivityP (((v,A0)::Gamma'0):: G & Gamma'); auto.
PPermut_LF_simpl. rew_app. transitivityP (Gamma' :: Gamma'0 :: G);
PPermut_LF_simpl; auto. transitivityP (Gamma'0 :: Gamma' :: G);
rew_app; PPermut_LF_simpl; auto. rew_app. constructor; auto.
PPermut_LF_simpl.
destruct IHHT with (M0:=M0) (A0:=A0) (v:=v); auto.
apply t; auto. apply PPermutationG_LF with (G:=emptyEquiv_LF G'0);
auto.
transitivityP (emptyEquiv_LF (G0 & Gamma')).
  apply PPermut_emptyEquiv_LF; auto.
apply PPermut_emptyEquiv_LF; auto.
transitivityP (G0 & Gamma'0); auto.
(* <> *)
assert ({ t |
  fst (fst t) *=* (v, A0)::Gamma'0 /\ G = snd (fst t) & fst (fst t) ++ (snd t)})
  as HP.
  apply PPermut_LF_split_neq_T with (Gamma:=Gamma) (G':=G0);
    auto; transitivityP G'; auto.
destruct HP as (t, (HPa, HPb)); destruct t as (t', GT);
destruct t' as (Gamma'', GH); simpl in *.
assert (GH & Gamma'' ++ GT ~=~ GH & ((v, A0)::Gamma'0) ++ GT)
  by PPermut_LF_simpl;
apply t_unbox_fetch_LF with (G:=GH ++ GT & (Gamma'0)) (Gamma:=Gamma).
subst;
apply ok_Bg_LF_PPermut with
  (G:= (((Gamma) :: (GH & (Gamma') ++ GT)) & (Gamma'0))).
apply ok_Bg_LF_permut_no_last_spec with (v:=v)(A:=A0).
apply ok_Bg_LF_PPermut with
  (G:=(Gamma):: (GH & (Gamma'') ++ GT) & (Gamma')); auto.
constructor; auto. PPermut_LF_simpl.
PPermut_LF_simpl.
destruct IHHT with (M0:=M0) (A0:=A0) (v:= v); auto.
eapply t0 with (Gamma'0:=Gamma'0) (G0:=GH ++ GT & Gamma')
  (G':=GH ++ GT & Gamma' & Gamma);subst; try PPermut_LF_simpl.
assert (GH ++ Gamma'' :: GT & Gamma ~=~ G0 & Gamma'').
  transitivityP G'; rew_app in *; auto.
transitivityP  (G0 & ((v, A0) :: Gamma'0)); auto.
assert (GH ++ GT & Gamma ~=~ G0).
  apply PPermut_LF_last_rev_simpl with (a:=Gamma'').
  transitivityP (GH ++ Gamma'' :: GT & Gamma);
    auto; PPermut_LF_simpl.
apply PPermutationG_LF with (G := emptyEquiv_LF G'0); auto.
transitivityP (emptyEquiv_LF (G0 & Gamma')).
apply PPermut_emptyEquiv_LF; auto.
transitivityP (emptyEquiv_LF (GH++GT& Gamma & Gamma'));
apply PPermut_emptyEquiv_LF; PPermut_LF_simpl; auto.
transitivityP ( G0 & Gamma'0); auto.
rew_app; PPermut_LF_simpl; apply PPermut_LF_last_rev_simpl
  with (a:=(v,A0)::Gamma'0). transitivityP G'; auto.
transitivityP (G & Gamma); auto; subst;
  PPermut_LF_simpl.
Qed.

Lemma subst_t_LF_preserv_types_inner:
forall G Gamma A B M N v
  (H_lc_t: lc_t_LF M)
  (HT: G |= (v, A) :: Gamma |- N ::: B)
  (HM: emptyEquiv_LF G |= nil |- M ::: A),
  G |= Gamma |- [M//fte v] N ::: B.
intros; eapply subst_t_LF_preserv_types with (Gamma := (v, A) :: Gamma); eauto.
Qed.

Lemma subst_t_LF_preserv_types_outer:
forall G0 G G' G'' Gamma Gamma' A B M N v
  (H_lc_t: lc_t_LF M)
  (G0G: G ~=~ (G0 & ((v, A) :: Gamma')))
  (G0G': G' ~=~ (G0 & Gamma))
  (G0G'': G'' ~=~ (G0 & Gamma'))
  (HM: emptyEquiv_LF G' |= nil |- M ::: A)
  (HT: G |= Gamma |- N ::: B),
  G'' |= Gamma |- [M // fte v] N ::: B.
intros; eapply subst_t_LF_preserv_types; eauto.
Qed.

Lemma merge_LF_preserv_types:
forall G Gamma M A
  (H: G |= Gamma |- M ::: A),
  (* outer *)
  (forall G0 G1 Gamma0 Delta0,
    G ~=~ Gamma0::Delta0::G0 ->
    G1 ~=~ (Gamma0++Delta0) :: G0 ->
    G1 |= Gamma |- M ::: A) *
  (* new or old - by PermutationGamma_LF *)
  (forall G0 Delta0,
    G ~=~ Delta0 :: G0 ->
    G0 |= Gamma ++ Delta0 |- M ::: A).
intros; induction H; repeat split; intros.
(* hyp *)
constructor; auto.
eapply ok_Bg_LF_concat with (G0:=Gamma::G0) (c1:=Gamma0) (c2:=Delta0)
  (G1:=Gamma::G) (G2:=Gamma::G1);
eauto. transitivityP (Gamma ::Gamma0 :: Delta0 :: G0); auto; PPermut_LF_simpl.
transitivityP (Gamma::(Gamma0 ++ Delta0) :: G0) ; PPermut_LF_simpl.
constructor.
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G); eauto.
rewrite Mem_app_or_eq; left; auto.
(* lam *)
apply t_lam_LF with (L:=L).
eapply ok_Bg_LF_concat with (G0:=Gamma::G0) (G1:=Gamma::G); eauto.
transitivityP (Gamma::Gamma0 :: Delta0 :: G0); auto; PPermut_LF_simpl.
transitivityP (Gamma:: (Gamma0 ++ Delta0) :: G0); auto; PPermut_LF_simpl.
intros; eapply X; eauto.
apply t_lam_LF with (L:=L).
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G); eauto.
intros; eapply X; eauto.
(* appl *)
apply t_appl_LF with (A:=A).
eapply ok_Bg_LF_concat with (G0:=Gamma::G0) (G1:=Gamma::G) (c1:=Gamma0)
  (c2:=Delta0); eauto;
try rewrite H2 || rewrite H1; eauto; PPermut_LF_simpl.
eapply IHtypes_LF1; eauto.
eapply IHtypes_LF2; eauto.
apply t_appl_LF with (A:=A).
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G); eauto.
eapply IHtypes_LF1; eauto.
eapply IHtypes_LF2; eauto.
(* box *)
constructor.
eapply ok_Bg_LF_concat with (G0:=G0 & Gamma) (G1:=G & Gamma)
  (c1:=Gamma0) (c2:=Delta0); eauto.
transitivityP (Gamma ::Gamma0 :: Delta0 :: G0); auto; PPermut_LF_simpl.
transitivityP (Gamma::(Gamma0 ++ Delta0) :: G0) ; PPermut_LF_simpl.
eapply IHtypes_LF with (G0:=G0 & Gamma) (Gamma0:=Gamma0) (Delta0:=Delta0);
eauto.
transitivityP (Gamma ::Gamma0 :: Delta0 :: G0); auto; PPermut_LF_simpl.
transitivityP (Gamma::(Gamma0 ++ Delta0) :: G0) ; PPermut_LF_simpl.
constructor.
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=G & Gamma)
  (c1:=Gamma) (c2:=Delta0); eauto; try PPermut_LF_simpl.
eapply IHtypes_LF with (G0:=G0) (Gamma0:=Gamma)
  (Delta0:=Delta0); eauto.
transitivityP (Delta0 :: G0 & Gamma); auto; PPermut_LF_simpl.
PPermut_LF_simpl.
(* unbox *)
constructor.
eapply ok_Bg_LF_concat with (G0:=Gamma::G0) (G1:=Gamma::G)
  (c1:=Gamma0)(c2:=Delta0); eauto;
try rewrite H0 || rewrite H1; PPermut_LF_simpl.
eapply IHtypes_LF; eauto.
constructor.
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G); eauto.
eapply IHtypes_LF; eauto.
(* Gamma *=* Gamma0 \/ Gamma *=* Gamma1 \/ neither *)
assert (G & Gamma ~=~ Gamma0 :: Delta0 :: G0).
  transitivityP G'; auto.
assert (( prod (Gamma *=* Gamma0) (G ~=~ Delta0::G0)) +
        ( prod (Gamma *=* Delta0)  (G ~=~ Gamma0::G0)) +
        {t | Gamma *=* fst (fst t) /\ G0 = snd (fst t) & fst (fst t) ++ snd t}).
  assert ({Gamma *=* Gamma0} + {~ Gamma *=* Gamma0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  assert ({Gamma *=* Delta0} + {~ Gamma *=* Delta0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  destruct H3. left; left; split; auto.
  apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Gamma0); auto. transitivityP (Gamma0 :: Delta0 :: G0); auto;
                          PPermut_LF_simpl.
  destruct H4.
  left; right; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Delta0); auto; transitivityP (Gamma0 :: Delta0 :: G0); auto;
                          PPermut_LF_simpl.
  right.
  assert (G & Gamma ~=~ G0 & Delta0 & Gamma0)
    by (transitivityP (Gamma0 :: Delta0 :: G0); auto;
                          PPermut_LF_simpl).
  apply PPermut_LF_symmetric in H3.
  apply PPermut_LF_split_neq_T in H3; auto.
  destruct H3 as (t, (H3, H4)); destruct t; destruct p0; simpl in *.
  assert (G0 & Delta0 ~=~ (l1 ++ l) & Gamma).
    rewrite H4; PPermut_LF_simpl.
  apply PPermut_LF_split_neq_T in H5; auto.
  destruct H5 as (t, (H5, H6)); destruct t; destruct p0; simpl in *.
  exists (l3, l4, l2); split; auto; symmetry; auto.
  intro nn; symmetry in nn; elim n0; auto.
  intro nn; symmetry in nn; elim n; auto.
destruct H3. destruct s.
destruct p0;
apply t_unbox_fetch_LF with (G:=G0) (Gamma:=Gamma0++Delta0).
eapply ok_Bg_LF_concat
 with (G0:=G0 & Gamma') (G1:=Gamma::G & Gamma'); eauto.
transitivityP (Gamma0::G & Gamma'); auto; PPermut_LF_simpl.
apply PermutationGamma_LF with (Gamma:=Gamma++Delta0); auto.
eapply IHtypes_LF. PPermut_LF_simpl.
transitivityP ((Gamma0 ++ Delta0) :: G0); auto; PPermut_LF_simpl.
destruct p0.
apply t_unbox_fetch_LF with (G:=G0) (Gamma:=Delta0++Gamma0).
eapply ok_Bg_LF_concat
 with (G0:=G0 & Gamma') (G1:=Gamma::G & Gamma'); eauto.
transitivityP (Gamma::Gamma0::G0 & Gamma'); auto; PPermut_LF_simpl.
apply PermutationGamma_LF with (Gamma:=Gamma++Gamma0); auto.
eapply IHtypes_LF. PPermut_LF_simpl.
transitivityP ( (Gamma0 ++ Delta0) :: G0); auto; PPermut_LF_simpl.
destruct s. destruct x; destruct p0; simpl in *. destruct a.
apply t_unbox_fetch_LF with (G:=(Gamma0++Delta0)::l1++l) (Gamma:=l0).
eapply ok_Bg_LF_concat with (G0:=G0 & Gamma') (G1:=Gamma::G & Gamma')
  (c1:=Gamma0) (c2:=Delta0); subst; auto.
transitivityP ((G & Gamma) & Gamma'); [ | PPermut_LF_simpl].
transitivityP ((Gamma0 :: Delta0 :: l1 & l0 ++ l) & Gamma'); PPermut_LF_simpl.
transitivityP G'; auto. transitivityP (Gamma0 :: Delta0 :: l1 & l0 ++ l); auto.
PPermut_LF_simpl.
transitivityP ((Gamma0++Delta0)::l0::l1++l & Gamma'); [PPermut_LF_simpl |].
rew_app; auto.
apply PermutationGamma_LF with (Gamma:=Gamma); auto.
assert (G ~=~ Gamma0::Delta0::l1 ++ l).
  subst; apply PPermut_LF_last_rev with (Gamma:=Gamma) (Gamma':=l0); auto.
  transitivityP (Gamma0 :: Delta0 :: l1 & l0 ++ l); auto; PPermut_LF_simpl.
eapply IHtypes_LF with (Gamma0:=Gamma0) (Delta0:=Delta0) (G0:=l1 ++l & Gamma');
eauto. PPermut_LF_simpl. PPermut_LF_simpl.
transitivityP ((Gamma0 ++ Delta0) :: G0); auto; subst; PPermut_LF_simpl.
assert ((prod (Gamma *=* Delta0)  (G ~=~ G0)) +
        {t | fst (fst t) *=* Gamma /\ G0 = snd(fst t) & fst (fst t) ++ snd t}).
  assert ({Gamma *=* Delta0} + {~ Gamma *=* Delta0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  destruct H1. left; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Delta0); auto. transitivityP G'; auto. transitivityP (Delta0::G0);
                                                  auto; PPermut_LF_simpl.
  right.
  assert (G & Gamma ~=~ G0 & Delta0).
  transitivityP G'; auto; transitivityP (Delta0::G0); auto; PPermut_LF_simpl.
  apply PPermut_LF_symmetric in H1.
  apply PPermut_LF_split_neq_T in H1; auto.
  intro nn; symmetry in nn; elim n; auto.
destruct H1.
destruct p0. constructor.
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G & Gamma'); eauto.
transitivityP (Gamma'::Delta0::G); auto; PPermut_LF_simpl.
apply PermutationGamma_LF with (Gamma:=Gamma++Gamma').
eapply IHtypes_LF.
transitivityP (Gamma'::G); auto; PPermut_LF_simpl.
permut_simpl; auto.
destruct s as (t, (H3a, H3b)); destruct t; destruct p0; simpl in *.
apply t_unbox_fetch_LF with (G:=l1++l) (Gamma:=Gamma).
eapply ok_Bg_LF_concat with (G0:=Gamma::(l1++l)) (G1:=Gamma::G & Gamma')
  (c1:=Gamma')(c2:=Delta0);
eauto.
transitivityP (G & Gamma & Gamma'); auto. transitivityP (G' & Gamma');
[ | PPermut_LF_simpl]. transitivityP (Delta0 :: G0 & Gamma');
PPermut_LF_simpl. subst; PPermut_LF_simpl.
PPermut_LF_simpl.
eapply IHtypes_LF with (Gamma0:=Gamma') (Delta0:=Delta0) (G0:= l1++l);
subst; try PPermut_LF_simpl. Focus 2. subst; PPermut_LF_simpl.
apply PPermut_LF_last_rev_simpl with Gamma.
transitivityP G'; auto.
transitivityP (Delta0 :: l1 & l0 ++ l); auto.
PPermut_LF_simpl.
Qed.

Lemma merge_LF_preserv_types_outer:
forall G G0 G1 Gamma Gamma0 Delta0 M A,
  G |= Gamma |- M ::: A ->
  G ~=~ Gamma0 :: Delta0 :: G0 ->
  G1 ~=~ (Gamma0 ++ Delta0) :: G0 ->
  G1 |= Gamma |- M ::: A.
intros; eapply merge_LF_preserv_types; eauto.
Qed.

Lemma merge_LF_preserv_types_new:
forall G G0 Gamma Delta M A,
  G |= Gamma |- M ::: A ->
  G ~=~ Delta::G0 ->
  G0 |= Gamma++Delta |- M ::: A.
intros; eapply merge_LF_preserv_types with (G:=G) (Gamma:=Gamma); eauto.
Qed.

Lemma merge_LF_preserv_types_old:
forall G G0 Gamma Delta M A,
  G |= Delta |- M ::: A ->
  G ~=~ Gamma::G0 ->
  G0 |= Gamma++Delta |- M ::: A.
intros;
apply PermutationGamma_LF with (Gamma:=Delta++Gamma).
eapply merge_LF_preserv_types; eauto.
auto.
Qed.

Lemma Progress_LF:
forall G M A
  (H_lc_t: lc_t_LF M)
  (HT: emptyEquiv_LF G |= nil |- M ::: A),
  value_LF M + (sigT (fun x => M |-> x)).
(* sigT (fun x => .. ) = { N & M |-> N}, but in tlc & is used for lists... *)
intros;
remember (@nil (var * ty)) as Ctx;
generalize dependent Ctx;
generalize dependent A;
generalize dependent G;
induction M; intros; eauto using value_LF;
inversion HeqCtx; subst.
(* hyp *)
inversion HT; subst;
rewrite Mem_nil_eq in H3;
contradiction.
(* appl *)
right; inversion HT; subst;
edestruct IHM1 with (A := A0 ---> A); eauto;
[inversion H_lc_t; subst; auto |
 inversion v; subst; inversion H4; subst |
 destruct s];
eexists; constructor; eauto;
inversion H_lc_t; auto; inversion H5; auto.
(* unbox *)
right; inversion HT; subst.
edestruct IHM with (A := [*]A); eauto; try inversion H_lc_t; auto; eauto.
inversion v; subst; inversion H3; subst; eexists; constructor; eauto;
inversion H_lc_t; inversion H2; auto.
destruct s; eexists; constructor; eauto;
inversion H_lc_t; auto.
assert (Gamma = nil) by
  ( apply emptyEquiv_LF_permut_empty with
    (G:= G0 & Gamma) (G':=G); auto;
    apply Mem_last); subst.
destruct IHM with (A := [*]A)
                  (Ctx := (@nil (var * ty)))
                  (G := G0 & nil);
eauto.
inversion H_lc_t; auto.
assert (emptyEquiv_LF (G0 & nil) = G0 & nil)
  by (eapply emptyEquiv_LF_PPermut_eq; eauto); rewrite H0; auto.
inversion v; subst; inversion H1; subst;
eexists; constructor; eauto; inversion H_lc_t; inversion H3; auto.
destruct s; eexists; constructor; eauto;
inversion H_lc_t; auto.
Qed.

Lemma Preservation_LF:
forall G M N A
  (HT: emptyEquiv_LF G |= nil |- M ::: A)
  (HS: M |-> N),
  emptyEquiv_LF G |= nil |- N ::: A.
intros; generalize dependent N.
remember (emptyEquiv_LF G) as G';
remember (@nil (var*ty)) as Gamma.
generalize dependent G.
induction HT; intros;
inversion HS; subst;
try (econstructor; eauto).

(* appl_lam *)
inversion HT1; subst;
unfold open_LF in *;
assert { v | v \notin L \u used_vars_te_LF M0} as HF by apply Fresh;
destruct HF as (v_fresh);
rewrite subst_t_neutral_free_LF with (v:=v_fresh);
[ eapply subst_t_LF_preserv_types_inner; eauto |
  rewrite notin_union in n; destruct n]; auto;
rewrite <- double_emptyEquiv_LF; auto.

(* unbox_box *)
inversion HT; subst;
replace (@nil (var * ty)) with (nil ++ (@nil (prod var ty)))
  by (rew_app; auto);
apply merge_LF_preserv_types_old with (G:=emptyEquiv_LF G0 & nil);
rew_app; auto.
transitivityP (emptyEquiv_LF (G0&nil)).
  rewrite emptyEquiv_LF_rewrite; auto.
  transitivityP (emptyEquiv_LF (nil :: G0)); auto.

apply PPermut_emptyEquiv_LF; PPermut_LF_simpl.

inversion HT; subst;
replace (@nil (var * ty)) with (nil ++ (@nil (prod var ty)))
  by (rew_app; auto);
apply merge_LF_preserv_types_old with (G:=G & nil & Gamma);
auto. transitivityP (nil :: G & Gamma); auto.
apply ok_Bg_LF_nil; apply ok_Bg_LF_empty.
assert (Gamma = nil).
  apply emptyEquiv_LF_PPermut in p; auto.
subst. replace (emptyEquiv_LF G0) with (G & nil).
apply IHHT with (G0:=G0); auto.
apply emptyEquiv_LF_PPermut_equal; auto.
apply emptyEquiv_LF_PPermut_equal; auto.
Qed.

Lemma value_no_step:
forall M,
  value_LF M ->
  forall N , M |-> N ->
             False.
induction M; intros;
try inversion H; subst;
inversion H0; subst;
rewrite IHM; eauto.
Qed.

Lemma lc_t_step_LF:
forall M N,
  lc_t_LF M ->
  M |-> N ->
  lc_t_LF N.
induction M; intros; inversion H0; inversion H; subst; try constructor; eauto.
apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
eapply IHM; eauto.
Qed.

Lemma types_LF_lc_t_LF:
forall G Gamma M A,
  G |= Gamma |- M ::: A -> lc_t_LF M.
intros; induction X; constructor; try apply IHHT;
unfold open_LF in *; auto.
assert { x |  x \notin L} by apply Fresh; destruct H1;
assert (x \notin L) by auto;
specialize H0 with x; apply H0 in H1;
apply lc_t_n_LF_subst_t in H0; auto; constructor.
Qed.
