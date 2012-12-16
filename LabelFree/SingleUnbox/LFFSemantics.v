Require Import LFFSubstitution.
Require Import LFFSyntax.
Require Import LFFOkLib.

Require Import LibTactics.

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
  (H: forall v, v \notin L ->
    G |= (v, A)::Gamma |- M ^t^ (hyp_LF (fte v)) ::: B),
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
    G' |= Gamma' |- unbox_LF M ::: A

| t_here_LF: forall A G Gamma M
  (Ok: ok_Bg (Gamma :: G))
  (H: G |= Gamma |- M ::: A),
  G |= Gamma |- here_LF M ::: <*> A

| t_get_here_LF: forall A G Gamma Gamma' M
  (Ok: ok_Bg (Gamma :: G & Gamma'))
  (H: G & Gamma' |= Gamma |- M ::: A),
  forall G', G & Gamma ~=~ G' ->
    G' |= Gamma' |- here_LF M ::: <*> A

| t_letdia_LF: forall L A B G Gamma M N
  (Ok_Bg: ok_Bg (Gamma :: G))
  (HT1: G |= Gamma |- M ::: <*> A)
  (HT2: forall G' v, v \notin L ->
    ((v, A) :: nil) :: G ~=~ G' ->
    G' |= Gamma |- N ^t^ (hyp_LF (fte v)) ::: B),
  G |= Gamma |- letdia_LF M N ::: B

| t_letdia_get_LF: forall L A B G Gamma Gamma' M N
  (Ok_Bg: ok_Bg (Gamma :: G & Gamma'))
  (HT1: G & Gamma' |= Gamma |- M ::: <*> A)
  (HT2: forall v, v \notin L ->
    ((v, A) :: nil) :: G & Gamma |= Gamma' |-
      N ^t^ (hyp_LF (fte v))::: B),
  forall G0, G & Gamma ~=~ G0 ->
    G0 |= Gamma' |- letdia_LF M N ::: B

where " G '|=' Gamma '|-' M ':::' A" := (types_LF G Gamma M A).

Inductive value_LF: te_LF -> Prop :=
| val_lam: forall A M, value_LF (lam_LF A M)
| val_box: forall M, value_LF (box_LF M)
| val_here: forall M, value_LF M -> value_LF (here_LF M)
.

Reserved Notation " M |-> N " (at level 70).

Inductive step_LF: te_LF -> te_LF -> Prop :=

| red_appl_lam_LF: forall M N A,
  lc_t_n_LF 1 M -> lc_t_LF N ->
  appl_LF (lam_LF A M) N |-> [N // bte 0] M

| red_unbox_box_LF: forall M,
  lc_t_LF M ->
  unbox_LF (box_LF M)|-> M

| red_letdia_here_LF: forall M N ,
  lc_t_LF M -> lc_t_n_LF 1 N ->
  letdia_LF (here_LF M) N |-> N ^t^ M

| red_appl_LF: forall M M' N,
  lc_t_LF M -> lc_t_LF N ->
  M |-> M'->
  appl_LF M N |-> appl_LF M' N

| red_unbox_LF: forall M M',
  lc_t_LF M -> M |-> M' ->
  unbox_LF M |-> unbox_LF M'

| red_here_LF: forall M M' ,
  lc_t_LF M -> M |-> M' ->
  here_LF M |-> here_LF M'

| red_letdia_LF: forall M M' N,
  lc_t_LF M -> lc_t_n_LF 1 N ->
  M |-> M'->
  letdia_LF M N |-> letdia_LF M' N

where " M |-> N " := (step_LF M N ).

Inductive steps_LF : te_LF -> te_LF -> Prop :=
| single_step_LF: forall M M', M |-> M' -> steps_LF M M'
| multi_step_LF: forall M M' M'',
  M |-> M' -> steps_LF M' M'' -> steps_LF M M''
.

(* Move it! *)

Definition used_vars_ctx_LF (L: bg_LF) :=
  map fst (concat L).

Fixpoint used_vars_te_LF (M: te_LF) : fset var :=
match M with
| hyp_LF (fte v) => \{v}
| hyp_LF (bte _) => \{}
| lam_LF _ M => used_vars_te_LF M
| appl_LF M N => used_vars_te_LF M \u used_vars_te_LF N
| box_LF M => used_vars_te_LF M
| unbox_LF M => used_vars_te_LF M
| here_LF M => used_vars_te_LF M
| letdia_LF M N => used_vars_te_LF M \u used_vars_te_LF N
end.


Fixpoint emptyEquiv (G: list (list (var * ty))) :=
match G with
| nil => nil
| a::G' => (@nil (var * ty)) :: emptyEquiv G'
end.


Lemma ok_Bg_PPermut:
forall G G',
  ok_Bg G -> G ~=~ G' -> ok_Bg G'.
Admitted.

Lemma ok_Bg_fresh:
forall G Gamma x A,
  ok_Bg (Gamma::G) ->
  ~ Mem x (used_vars_ctx_LF (Gamma::G)) ->
  ok_Bg (((x, A) :: Gamma)::G).
Admitted.

Lemma ok_Bg_nil:
forall G,
  ok_Bg G ->
  ok_Bg (nil::G).
Admitted.

Hint Resolve ok_Bg_nil.

Lemma emptyEquiv_permut_empty:
forall G G',
  G ~=~ emptyEquiv G' ->
  forall C, Mem C G -> C = nil.
Admitted.
(* /end *)

Lemma PPermutationG:
forall G Gamma M A G',
  G |= Gamma |- M ::: A ->
  G ~=~ G' ->
  G' |= Gamma |- M ::: A.
intros; generalize dependent G'; induction H; intros; simpl in *.

constructor; [apply ok_Bg_PPermut with (G:=Gamma::G)| ]; auto.
skip. (* PPermut_simpl *)

apply t_lam_LF with (L:=L);
[apply ok_Bg_PPermut with (G:=Gamma::G)| ]; auto. skip.

apply t_appl_LF with (A:=A);
[apply ok_Bg_PPermut with (G:=Gamma::G)| |]; auto. skip.

constructor;
[apply ok_Bg_PPermut with (G:=G & Gamma)|]; auto. skip.
apply IHtypes_LF. skip.

constructor;
[apply ok_Bg_PPermut with (G:=Gamma::G)|]; auto. skip.

apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto.
skip.

constructor;
[apply ok_Bg_PPermut with (G:=Gamma::G)|]; auto. skip.

apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto.
skip.

apply t_letdia_LF with (A:=A) (L:=L);
[apply ok_Bg_PPermut with (G:=Gamma::G) | | ]; auto. skip.
intros. apply HT2; auto. skip.

apply t_letdia_get_LF with (A:=A) (L:=L) (G:=G) (Gamma:=Gamma);
[apply ok_Bg_PPermut with (G:=Gamma::G & Gamma') | | | ]; auto. skip.
skip.
Qed.

Lemma PermutationGamma:
forall G Gamma M A Gamma',
  G |= Gamma |- M ::: A ->
  Gamma *=* Gamma' ->
  G |= Gamma' |- M ::: A.
intros. generalize dependent Gamma'.
induction H; intros; simpl in *.

constructor;
[apply ok_Bg_PPermut with (G:=Gamma::G) |
 apply Mem_permut with (l:=Gamma)]; auto. skip.

apply t_lam_LF with (L:=L);
[apply ok_Bg_PPermut with (G:=Gamma::G) |]; auto.
skip.

apply t_appl_LF with (A:=A);
[apply ok_Bg_PPermut with (G:=Gamma::G) | |]; auto.
skip.

constructor;
[apply ok_Bg_PPermut with (G:=G & Gamma) |]; auto.
skip. apply PPermutationG with (G:=G & Gamma);
auto. skip.

constructor;
[apply ok_Bg_PPermut with (G:= Gamma :: G) |]; auto.
skip.

apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma);
[apply ok_Bg_PPermut with (G:= Gamma :: G & Gamma') | |]; auto.
skip. apply PPermutationG with (G:=G & Gamma'); auto.
skip.

constructor;
[apply ok_Bg_PPermut with (G:= Gamma :: G) |]; auto.
skip.

apply t_get_here_LF with (G:=G) (Gamma:=Gamma);
[apply ok_Bg_PPermut with (G:= Gamma :: G & Gamma') | |]; auto.
skip. apply PPermutationG with (G:=G & Gamma'); auto.
skip.

apply t_letdia_LF with (A:=A) (L:=L);
[apply ok_Bg_PPermut with (G:= Gamma :: G) | |]; auto.
skip.

apply t_letdia_get_LF with (A:=A) (L:=L) (G:=G) (Gamma:=Gamma);
[apply ok_Bg_PPermut with (G:= Gamma :: G & Gamma') | | |]; auto.
skip.
apply PPermutationG with (G:=G & Gamma'); auto. skip.
Qed.


Lemma WeakeningG:
forall G Gamma M A Delta,
  G |= Gamma |- M ::: A ->
  ok_Bg (Gamma::Delta::G) ->
  Delta :: G |= Gamma |- M ::: A.
intros; generalize dependent Delta; induction H;
intros; simpl in *; eauto using types_LF.

apply t_lam_LF with (L:=L \u from_list(used_vars_ctx_LF (Gamma:: Delta :: G)));
auto; intros;
apply H0; auto; apply ok_Bg_fresh; auto;
apply notin_Mem; rewrite notin_union in H2; destruct H2; auto.

constructor;
[apply ok_Bg_PPermut with (G:=Gamma::Delta::G) | rew_app ];
auto. skip. apply IHtypes_LF; apply ok_Bg_nil;
apply ok_Bg_PPermut with (G:=Gamma::Delta::G); auto. skip.

apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=Delta :: G);
[apply ok_Bg_PPermut with (G:=Gamma'::Delta::G') | |]; auto.
skip. rew_app; apply IHtypes_LF; eapply ok_Bg_PPermut; eauto.
skip. skip.

apply t_get_here_LF with (Gamma:=Gamma) (G:=Delta :: G);
[apply ok_Bg_PPermut with (G:=Gamma'::Delta::G') | |]; auto.
skip. rew_app; apply IHtypes_LF; eapply ok_Bg_PPermut; eauto.
skip. skip.

apply t_letdia_LF with
  (L:=L \u from_list (used_vars_ctx_LF (Gamma :: Delta :: G))) (A:=A);
auto; intros.
apply PPermutationG with (G:=Delta :: ((v, A)::nil) :: G).
apply H0; auto.
skip. apply ok_Bg_PPermut with (G:=((v,A)::nil) :: Gamma :: Delta :: G).
apply ok_Bg_fresh; [apply ok_Bg_nil | ]; auto.
apply notin_Mem; unfold used_vars_ctx_LF in *; rew_concat in *; eauto.
skip. skip.

apply t_letdia_get_LF with
  (L:=L \u from_list (map fst (Gamma' ++ Delta ++ concat G0)))
  (A:=A) (G:=Delta::G) (Gamma:=Gamma);
[apply ok_Bg_PPermut with (G:=Gamma'::Delta::G0) | | |]; auto.
skip. apply IHtypes_LF;
apply ok_Bg_PPermut with (G:=Gamma'::Delta::G0); auto. skip.
intros. apply PPermutationG with (G:=Delta :: ((v, A) :: nil) :: G & Gamma).
apply H0; auto.
apply ok_Bg_PPermut with (G:= ((v, A)::nil) :: Gamma' :: Delta :: G0).
apply ok_Bg_fresh; [apply ok_Bg_nil | ]; auto.
apply notin_Mem; unfold used_vars_ctx_LF in *; rew_concat in *; eauto.
skip. skip. skip.
Qed.

Lemma WeakeningWithinContext:
forall G Gamma M A,
  G |= Gamma |- M ::: A ->
  (forall Delta Delta' G',
    G' & Delta ~=~ G ->
    ok_Bg (Gamma :: G' & (Delta ++ Delta')) ->
    G' & (Delta++Delta') |= Gamma |- M ::: A)
  /\
  (forall Gamma',
    ok_Bg ((Gamma++Gamma')::G) ->
    G |= Gamma ++ Gamma' |- M ::: A).
intros G Gamma M A H.
induction H; split; intros; subst.
constructor; auto.
constructor; auto; rewrite Mem_app_or_eq; left; auto.
apply t_lam_LF with
  (L:=L \u from_list
    (used_vars_ctx_LF (Gamma :: G' & (Delta ++ Delta'))));
auto; intros; eapply H0; eauto;
rew_app; apply ok_Bg_fresh; eauto; apply notin_Mem;
rewrite notin_union in H3; destruct H3; auto.
apply t_lam_LF with
  (L:=L \u from_list
    (used_vars_ctx_LF ((Gamma ++ Gamma') :: G)));
auto; intros; eapply H0; eauto;
rew_app; apply ok_Bg_fresh; eauto; apply notin_Mem;
rewrite notin_union in H2; destruct H2; auto.
econstructor; eauto; [eapply IHtypes_LF1 | eapply IHtypes_LF2]; eauto.
econstructor; eauto; [eapply IHtypes_LF1 | eapply IHtypes_LF2]; eauto.
econstructor;
[apply ok_Bg_PPermut with (G:=Gamma:: G' & (Delta++Delta')) | ];
auto. skip.
apply PPermutationG with (G:= ((G'& Gamma) & (Delta ++ Delta'))).
eapply IHtypes_LF. skip.
apply ok_Bg_nil; apply ok_Bg_PPermut with (G:=Gamma :: G' & (Delta ++ Delta'));
auto. skip. skip.
econstructor;
[apply ok_Bg_PPermut with (G:=(Gamma++Gamma'):: G) | ];
auto. skip.
eapply IHtypes_LF. skip.
apply ok_Bg_nil; apply ok_Bg_PPermut with (G:=(Gamma++Gamma') :: G);
auto. skip.
constructor; eauto; eapply IHtypes_LF; eauto.
constructor; eauto; eapply IHtypes_LF; eauto.
(* G'0 & Delta ~=~ G & Gamma -> either Delta *=* Gamma or .. well.. not *)
skip. (* We'll need some lemmas about permutation for this *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma);
[apply ok_Bg_PPermut with (G:=(Gamma'++Gamma'0):: G') | | ];
auto. skip.
eapply IHtypes_LF. skip.
apply ok_Bg_PPermut with (G:=(Gamma'++Gamma'0):: G'); auto. skip.
constructor; eauto; eapply IHtypes_LF; eauto.
constructor; eauto; eapply IHtypes_LF; eauto.
(* G'0 & Delta ~=~ G & Gamma -> either Delta *=* Gamma or .. well.. not *)
skip. (* We'll need some lemmas about permutation for this *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma);
[apply ok_Bg_PPermut with (G:=(Gamma'++Gamma'0):: G') | | ];
auto. skip.
eapply IHtypes_LF. skip.
apply ok_Bg_PPermut with (G:=(Gamma'++Gamma'0):: G'); auto. skip.
apply t_letdia_LF with (A:=A)
  (L:=L \u from_list (used_vars_ctx_LF (Gamma :: G' & (Delta ++ Delta'))));
auto; [apply IHtypes_LF | intros]; auto.
apply PPermutationG with (G:= (((v, A) :: nil) :: G') & (Delta ++ Delta')).
eapply H0 with (G':=((v, A)::nil) :: G' & Delta).
auto. skip. skip.
apply ok_Bg_PPermut with (G:=((v, A) :: nil) :: Gamma :: G' & (Delta ++Delta')).
apply ok_Bg_fresh. apply ok_Bg_nil; auto.
apply notin_Mem; unfold used_vars_ctx_LF in *; rew_concat in *; eauto.
skip. skip.
apply t_letdia_LF with (A:=A)
  (L:=L \u from_list (used_vars_ctx_LF ((Gamma++Gamma') :: G)));
auto; [apply IHtypes_LF | intros]; auto.
eapply H0; eauto.
apply ok_Bg_PPermut with (G:=((v, A) :: nil) :: (Gamma++Gamma') :: G).
apply ok_Bg_fresh. apply ok_Bg_nil; auto.
apply notin_Mem; unfold used_vars_ctx_LF in *; rew_concat in *; eauto.
skip.
(* same situation as with unbox_fetch and get_here *)
skip.
apply t_letdia_get_LF with (A:=A) (G:=G) (Gamma:=Gamma)
  (L:=L \u from_list(used_vars_ctx_LF ((Gamma' ++ Gamma'0) :: G0)));
[apply ok_Bg_PPermut with (G:=(Gamma'++Gamma'0):: G0) | | | ];
auto. skip.
eapply IHtypes_LF. skip.
apply ok_Bg_PPermut with (G:=(Gamma'++Gamma'0):: G0); auto. skip.
intros. eapply H0; eauto.
apply ok_Bg_PPermut with (G:=((v,A)::nil) :: (Gamma'++Gamma'0) :: G0).
apply ok_Bg_fresh. apply ok_Bg_nil; auto.
apply notin_Mem; unfold used_vars_ctx_LF in *; rew_concat in *; eauto.
skip.
Qed.

Lemma WeakeneningGamma:
forall G Gamma M A Gamma',
  G |= Gamma |- M ::: A ->
  ok_Bg ((Gamma++Gamma')::G) ->
  G |= Gamma ++ Gamma' |- M ::: A.
intros; eapply WeakeningWithinContext; eauto.
Qed.

Lemma WeakeningWithinG:
forall G Gamma M A Delta Delta',
  G & Delta |= Gamma |- M ::: A ->
  ok_Bg (Gamma :: G & (Delta ++ Delta')) ->
  G & (Delta++Delta')|= Gamma |- M ::: A.
intros; eapply WeakeningWithinContext; eauto. skip.
Qed.

Lemma subst_t_neutral_free:
forall M v n N
  (HT: v \notin used_vars_te_LF M),
  [ N // bte n] M = [N // fte v] [hyp_LF (fte v) // bte n] M.
Admitted.

Lemma subst_t_preserv_types:
forall G Gamma B M N v A
  (H_lc_t: lc_t_LF M)
  (HT: G |= Gamma |- N ::: B),
  (* "inner" substitution *)
  ( forall Gamma0,
    Gamma *=* ((v, A) :: Gamma0) ->
    emptyEquiv G |= nil |- M ::: A ->
    G |= Gamma0 |- [M // fte v] N ::: B)
  /\
  (* "outer" substitution *)
  ( forall G0 G' G'' Gamma',
    G ~=~ (G0 & ((v,A)::Gamma')) ->
    G' ~=~ (G0 & Gamma) ->
    G'' ~=~ (G0 & Gamma') ->
    emptyEquiv G' |= nil |- M ::: A ->
    G'' |= Gamma |- [M // fte v] N ::: B).
Admitted.

Lemma subst_t_preserv_types_inner:
forall G Gamma A B M N v
  (H_lc_t: lc_t_LF M)
  (HT: G |= (v, A) :: Gamma |- N ::: B)
  (HM: emptyEquiv G |= nil |- M ::: A),
  G |= Gamma |- [M//fte v] N ::: B.
intros; eapply subst_t_preserv_types with (Gamma := (v, A) :: Gamma); eauto.
Qed.

Lemma subst_t_preserv_types_outer:
forall G0 G G' G'' Gamma Gamma' A B M N v
  (H_lc_t: lc_t_LF M)
  (G0G: G ~=~ (G0 & ((v, A) :: Gamma')))
  (G0G': G' ~=~ (G0 & Gamma))
  (G0G'': G'' ~=~ (G0 & Gamma'))
  (HM: emptyEquiv G' |= nil |- M ::: A)
  (HT: G |= Gamma |- N ::: B),
  G'' |= Gamma |- [M // fte v] N ::: B.
intros; eapply subst_t_preserv_types; eauto.
Qed.

Lemma merge_preserv_types:
forall G Gamma M A
  (H: G |= Gamma |- M ::: A),
  (* outer *)
  (forall G0 G1 Gamma0 Delta0,
    G ~=~ Gamma0::Delta0::G0 ->
    G1 ~=~ (Gamma0++Delta0) :: G0 ->
    G1 |= Gamma |- M ::: A) /\
  (* new *)
  (forall G0 Delta0,
    G ~=~ Delta0 :: G0 ->
    G0 |= Gamma ++ Delta0 |- M ::: A) /\
  (* old *)
  (forall G0 Gamma0,
    G ~=~ Gamma0 :: G0 ->
    G0 |= Gamma0 ++ Gamma |- M ::: A).
intros; induction H; repeat split; intros.
Admitted.

Lemma merge_preserv_types_outer:
forall G G0 G1 Gamma Gamma0 Delta0 M A,
  G |= Gamma |- M ::: A ->
  G ~=~ Gamma0 :: Delta0 :: G0 ->
  G1 ~=~ (Gamma0 ++ Delta0) :: G0 ->
  G1 |= Gamma |- M ::: A.
intros; eapply merge_preserv_types; eauto.
Qed.

Lemma merge_preserv_types_new:
forall G G0 Gamma Delta M A,
  G |= Gamma |- M ::: A ->
  G ~=~ Delta::G0 ->
  G0 |= Gamma++Delta |- M ::: A.
intros; eapply merge_preserv_types with (G:=G) (Gamma:=Gamma); eauto.
Qed.

Lemma merge_preserv_types_old:
forall G G0 Gamma Delta M A,
  G |= Delta |- M ::: A ->
  G ~=~ Gamma::G0 ->
  G0 |= Gamma++Delta |- M ::: A.
intros; eapply merge_preserv_types; eauto.
Qed.

Lemma Progress:
forall G M A
  (H_lc_t: lc_t_LF M)
  (HT: emptyEquiv G |= nil |- M ::: A),
  value_LF M \/ exists N, M |-> N.
intros;
remember (@nil (var * ty)) as Ctx;
generalize dependent Ctx.
generalize dependent A;
generalize dependent G.
induction M; intros; eauto using value_LF;
inversion HeqCtx; subst.
(* hyp *)
inversion HT; subst.
rewrite Mem_nil_eq in H3;
contradiction.
(* appl *)
right; inversion HT; subst;
inversion H_lc_t; subst;
edestruct IHM1 with (A := A0 ---> A); eauto;
[inversion H0; subst; inversion H4; subst | inversion H0];
eexists; constructor; eauto;
inversion H3; subst; auto.
(* unbox *)
right; inversion HT; subst;
inversion H_lc_t; subst.
edestruct IHM with (A := [*]A); eauto;
[ inversion H0; subst; inversion H3; subst; inversion H3 |
  destruct H0];
eexists; constructor; eauto;
inversion H1; inversion H2; subst; auto.
assert (Gamma = nil) by
  ( apply emptyEquiv_permut_empty with
    (G:= G0 & Gamma) (G':=G); auto;
    apply Mem_last); subst.
destruct IHM with (A := [*]A)
                  (Ctx := (@nil (var * ty)))
                  (G := G0 & nil);
eauto.
assert (emptyEquiv (G0 & nil) = G0 & nil) by
  skip.
rewrite H0; auto.
inversion H0; subst; inversion H1; subst.
eexists; constructor; eauto. inversion H3; auto; subst.
destruct H0; eexists; econstructor; eauto.
(* here *)
inversion HT; subst;
inversion H_lc_t; subst.
edestruct IHM; eauto;
[left; econstructor | right; destruct H0; eexists];
eauto using step_LF.
assert (Gamma = nil) by
  ( apply emptyEquiv_permut_empty with
    (G:= G0 & Gamma) (G':=G); auto;
    apply Mem_last); subst;
destruct IHM with (A := A0)
                  (Ctx := (@nil (var*ty)))
                  (G := G0 & nil);
eauto.
assert (emptyEquiv (G0 & nil) = G0 & nil) by skip.
rewrite H0; auto.
left; inversion H0; subst; inversion H4; subst;
econstructor; eauto using step_LF.
right; destruct H0; eexists;
econstructor; eauto using step_LF.
(* letdia *)
right; inversion HT; subst;
inversion H_lc_t; subst.
edestruct IHM1 with (A := <*>A0); eauto;
[ inversion H0; subst; inversion HT1; subst |
  destruct H0];
eexists; constructor; eauto.
inversion H4; subst; auto.
inversion H4; subst; auto.
assert (Gamma = nil) by
  ( apply emptyEquiv_permut_empty with (G:= G0 & Gamma) (G':=G);
    auto; apply Mem_last); subst;
edestruct IHM1 with (G := G0 & nil)
                    (Ctx := (@nil (var*ty)))
                    (A := <*>A0); eauto;
assert ( emptyEquiv (G0 & nil) = G0 & nil) by skip.
rewrite H0; auto.
inversion H0; subst; inversion HT1; subst;
eexists; constructor; eauto;
inversion H4; subst; auto.
destruct H0;
eexists; econstructor; eauto.
Admitted. (* Existential variables *)

(* this is also to be moved *)
Lemma double_emptyEquiv:
forall G,
 emptyEquiv G = emptyEquiv (emptyEquiv G).
Admitted.
(* end *)

Lemma Preservation:
forall G M N A
  (HT: emptyEquiv G |= nil |- M ::: A)
  (HS: M |-> N),
  emptyEquiv G |= nil |- N ::: A.
intros; generalize dependent N.
remember (emptyEquiv G) as G';
remember (@nil (var*ty)) as Gamma.
generalize dependent G.
induction HT; intros;
inversion HS; subst;
try (econstructor; eauto).

(* appl_lam *)
inversion HT1; subst;
unfold open_LF in *;
assert (exists v, v \notin L \u used_vars_te_LF M0) as HF by apply Fresh;
destruct HF as (v_fresh);
rewrite subst_t_neutral_free with (v:=v_fresh);
[ eapply subst_t_preserv_types_inner; eauto |
  rewrite notin_union in H; destruct H]; auto;
rewrite <- double_emptyEquiv; auto.

(* unbox_box *)
inversion HT; subst;
replace (@nil (var * ty)) with (nil ++ (@nil (prod var ty)))
  by (rew_app; auto);
apply merge_preserv_types_old with (G:=emptyEquiv G0 & nil);
rew_app; auto. skip.

inversion HT; subst;
replace (@nil (var * ty)) with (nil ++ (@nil (prod var ty)))
  by (rew_app; auto);
apply merge_preserv_types_old with (G:=G & nil & Gamma);
auto. skip.

skip.

assert (Gamma = nil) by skip. (* from H *)
subst. replace (emptyEquiv G0) with (G & nil).
apply IHHT with (G0:=G0); auto.
skip. (* these are all just nils but we should probably do sth about it in
         the lemma statement *)
skip. (* this is really permut rewrite using H *)

(* here *)
skip.

assert (Gamma = nil) by skip. (* from H *)
subst. replace (emptyEquiv G0) with (G & nil).
apply IHHT with (G0:=G0); auto.
skip. (* these are all just nils but we should probably do sth about it in
         the lemma statement *)
skip. (* this is really permut rewrite using H *)

inversion HT; subst;
unfold open_LF in *;
assert (exists v, v \notin L \u used_vars_te_LF N) as HF by apply Fresh;
destruct HF as (v_fresh);
rewrite subst_t_neutral_free with (v:=v_fresh);
replace (@nil (var * ty)) with (nil ++ (@nil (prod var ty)))
  by (rew_app; auto).

apply merge_preserv_types_old with (G:=emptyEquiv G0 & nil);
rew_app; auto.
apply subst_t_preserv_types_outer with
  (A:=A) (G:=((v_fresh, A) :: nil) :: emptyEquiv G0) (G0:=emptyEquiv G0)
  (Gamma':=nil) (G':=emptyEquiv G0 & nil); eauto.
skip. skip. skip.
assert (emptyEquiv G0 & nil = emptyEquiv (G0 & nil)) by skip.
rewrite H1; rewrite <- double_emptyEquiv; rewrite <- H1.
replace (emptyEquiv G0 & nil) with (nil::emptyEquiv G0) by skip.
apply WeakeningG; auto.
apply HT2.
rewrite notin_union in H0; destruct H0; auto.
skip. skip.
rewrite notin_union in H0; destruct H0; auto.

apply merge_preserv_types_old with (G:=emptyEquiv G0 & nil);
rew_app; auto.
apply subst_t_preserv_types_outer with
  (A:=A) (G:=((v_fresh, A) :: nil) :: emptyEquiv G0) (G0:=emptyEquiv G0)
  (Gamma':=nil) (G':=emptyEquiv G0 & nil); eauto.
skip. skip. skip.
assert (Gamma = nil) by skip; subst.
assert (emptyEquiv G0 & nil = emptyEquiv (G0 & nil)) by skip.
rewrite H1; rewrite <- double_emptyEquiv; rewrite <- H1.
replace (emptyEquiv G0 & nil) with (nil::emptyEquiv G0) by skip.
apply WeakeningG; auto. skip. (* rewrite by H7; exact H6 *)
apply HT2.
rewrite notin_union in H0; destruct H0; auto.
skip. skip.

rewrite notin_union in H0; destruct H0; auto.

inversion HT; subst;
unfold open_LF in *;
assert (exists v, v \notin L \u used_vars_te_LF N) as HF by apply Fresh;
destruct HF as (v_fresh);
rewrite subst_t_neutral_free with (v:=v_fresh);
replace (@nil (var * ty)) with (nil ++ (@nil (prod var ty)))
  by (rew_app; auto).
apply merge_preserv_types_old with (G:=emptyEquiv G1 & nil);
rew_app; auto.
apply subst_t_preserv_types_outer with
  (A:=A) (G:=((v_fresh, A) :: nil) :: emptyEquiv G1) (G0:=emptyEquiv G1)
  (Gamma':=nil) (G':=emptyEquiv G1 & nil); eauto.
skip. skip. skip.
assert (emptyEquiv G1 & nil = emptyEquiv (G1 & nil)) by skip.
rewrite H2; rewrite <- double_emptyEquiv; rewrite <- H2.
replace (emptyEquiv G1 & nil) with (nil::emptyEquiv G1) by skip.
apply WeakeningG; auto.
replace (emptyEquiv G1) with (G & Gamma) by skip.
assert (Gamma = nil) by skip; subst; auto.
skip.
replace (emptyEquiv G1) with (G & Gamma) by skip.
apply HT2; eauto.
skip. eauto.
apply merge_preserv_types_old with (G:=emptyEquiv G1 & nil);
rew_app; auto.
apply subst_t_preserv_types_outer with
  (A:=A) (G:=((v_fresh, A) :: nil) :: emptyEquiv G1) (G0:=emptyEquiv G1)
  (Gamma':=nil) (G':=emptyEquiv G1 & nil); eauto.
skip. skip. skip.
assert (emptyEquiv G1 & nil = emptyEquiv (G1 & nil)) by skip.
rewrite H2; rewrite <- double_emptyEquiv; rewrite <- H2.
replace (emptyEquiv G1 & nil) with (nil::emptyEquiv G1) by skip.
apply WeakeningG; auto.
replace (emptyEquiv G1) with (G & Gamma) by skip.
assert (Gamma = nil) by skip; subst; auto.
assert (Gamma0 = nil) by skip; subst; auto.
assert (G0 ~=~ G) by skip. (* from H8 *)
replace G with G0. auto. skip.
skip.
replace (emptyEquiv G1) with (G & Gamma) by skip.
apply HT2; eauto.
skip. eauto.
skip.
replace (emptyEquiv G1) with (G & Gamma) by skip.
assert (Gamma = nil) by skip; subst; eapply IHHT; auto.
skip.

intros. unfold open_LF in *.
assert (Gamma = nil) by skip; subst.
replace G' with (((v,A)::nil) :: emptyEquiv G1) by skip.
replace (emptyEquiv G1) with (G & nil) by skip.
apply HT2; eauto.
Admitted.