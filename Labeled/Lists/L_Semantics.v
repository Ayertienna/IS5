Add LoadPath "../..".
Require Import L_Substitution.
Require Import PermutLib.
Require Import LibTactics.
Require Import L_OkLib.
Require Import Relations.

Open Scope is5_scope.
Open Scope labeled_is5_scope.
Open Scope permut_scope.

Global Reserved Notation " Omega ';' Gamma '|-' M ':::' A '@' w " (at level 70).

Inductive types_L: worlds_L -> ctx_L -> te_L -> ty -> var -> Prop :=

| t_hyp_L: forall Omega Gamma v A w
  (Ok: ok_L Omega Gamma)
  (World: Mem w Omega)
  (HT: Mem (w, (v, A)) Gamma),
  Omega; Gamma |- hyp_L (fte v) ::: A @ w

| t_lam_L: forall L Omega Gamma w A B M
  (Ok: ok_L Omega Gamma)
  (HT: forall x, x \notin L ->
    Omega; (w, (x,A))::Gamma |- (M ^t^ (hyp_L (fte x))) ::: B @ w),
  Omega; Gamma |- lam_L A M ::: A ---> B @ w

| t_appl_L: forall Omega Gamma w A B M N
  (Ok: ok_L Omega Gamma)
  (HT1: Omega; Gamma |- M ::: A ---> B @ w)
  (HT2: Omega; Gamma |- N ::: A @ w),
  Omega; Gamma |- appl_L M N ::: B @ w

| t_box_L: forall L Omega Gamma w M A
  (Ok: ok_L Omega Gamma)
  (World: Mem w Omega)
  (HT: forall x, x \notin L ->
    (x :: Omega); Gamma |- (M ^w^ (fwo x)) ::: A @ x),
  Omega; Gamma |- box_L M ::: [*]A @ w

| t_unbox_L: forall Omega Gamma w M A
  (Ok: ok_L Omega Gamma)
  (HT: Omega; Gamma |- M ::: [*]A @ w),
  Omega; Gamma |- unbox_L M ::: A @ w

| t_fetch_L: forall Omega Gamma w w' M A
  (Ok: ok_L Omega Gamma)
  (HT: Omega; Gamma |- M ::: [*]A @ w)
  (Hin: Mem w' Omega),
  Omega; Gamma |- fetch_L (fwo w) M ::: [*]A @ w'

| t_here_L: forall Omega Gamma w M A
  (Ok: ok_L Omega Gamma)
  (HT: Omega; Gamma |- M ::: A @ w),
  Omega; Gamma |- here_L M ::: <*> A @ w

| t_get_L: forall Omega Gamma w w' M A
  (Ok: ok_L Omega Gamma)
  (HT: Omega; Gamma |- M ::: <*>A @ w)
  (Hin: Mem w' Omega),
  Omega; Gamma |- get_L (fwo w) M ::: <*>A @ w'

| t_letd_L: forall Lw Lt Omega Gamma w M N A B
  (Ok: ok_L Omega Gamma)
  (HT1: Omega; Gamma |- M ::: <*>A @ w)
  (HT2: forall t, t \notin Lt -> forall w', w' \notin Lw ->
    w' :: Omega; (w', (t, A)) :: Gamma |-
      ((N ^w^ (fwo w')) ^t^ (hyp_L (fte t)))  ::: B @ w),
  Omega; Gamma |-letd_L M N ::: B @ w

where " Omega ';' Gamma '|-' M ':::' A '@' w " := (types_L Omega Gamma M A w):
  labeled_is5_scope.

Inductive value_L: te_L -> Prop :=
| val_lam_L: forall A M, value_L (lam_L A M)
| val_box_L: forall M, value_L (box_L M)
| val_get_here_L: forall M w (HT: value_L M), value_L (get_L w (here_L M))
.

Global Reserved Notation " M |-> N " (at level 70).

Inductive step_L: te_L * vwo -> te_L * vwo -> Prop :=
| red_appl_lam_L: forall A M N w,
   lc_w_L M -> lc_t_L (M ^t^ N) ->
   lc_w_L N -> lc_t_L N ->
   (appl_L (lam_L A M) N, w) |-> (M ^t^ N, w)
| red_unbox_box_L: forall M w,
   lc_t_L M -> lc_w_L (M ^w^ w) ->
   (unbox_L (box_L M), w) |-> (M ^w^ w, w)
| red_letd_get_here_L: forall M N w w',
   lc_t_L M -> lc_w_L M ->
   lc_t_L (N ^t^ M) -> lc_w_L (N ^w^ w') -> value_L M ->
   (letd_L (get_L w' (here_L M)) N, w) |-> ((N ^w^ w') ^t^ M, w)
| red_appl_L: forall M N M' w (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   lc_t_L N -> lc_w_L N ->
   (appl_L M N, w) |-> (appl_L M' N, w)
| red_unbox_L: forall M M' w (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   (unbox_L M, w) |-> (unbox_L M', w)
| red_fetch_L: forall M M' w w'  (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   (fetch_L w M, w') |-> (fetch_L w M', w')
| red_fetch_val_L: forall w M w' (HVal: value_L M),
   lc_t_L M -> lc_w_L M ->
   (fetch_L w M, w') |-> (M, w')
| red_here_L: forall N N' w (HRed: (N, w) |-> (N',w)),
   lc_t_L N -> lc_w_L N ->
   (here_L N, w) |-> (here_L N', w)
| red_here_val_L: forall M w (HVal: value_L M),
   (here_L M, w) |-> (get_L w (here_L M), w)
| red_letd_L: forall M M' N w (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   lc_t_L (N ^t^ M) -> lc_w_L (N ^w^ w) ->
   (letd_L M N, w) |-> (letd_L M' N, w)
| red_get_L: forall w M M' w' (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   (get_L w M, w') |-> (get_L w M', w')
| red_get_val_L: forall w M w' w'',
   (get_L w (get_L w' M), w'') |-> (get_L w' M, w'')
where " M |-> N " := (step_L M N ) : labeled_is5_scope.

Inductive steps_L : te_L -> te_L -> vwo -> Prop :=
| step1_L: forall M N w, step_L (M, w) (N, w) -> steps_L M N w
| stepm_L: forall M M' N w,
             step_L (M, w) (M', w) -> steps_L M' N w ->
             steps_L M N w
.

Lemma WeakeningGamma_L:
forall Omega Gamma M A w Gamma'
  (H: Omega; Gamma |- M ::: A @ w)
  (Ok: ok_L Omega (Gamma ++ Gamma')),
  forall Delta,
    Delta *=* Gamma ++ Gamma' ->
    Omega; Delta |- M ::: A @ w.
intros; generalize dependent Gamma'; generalize dependent Delta;
induction H; intros.
(* hyp *)
constructor;
[ eapply ok_L_permut; [ | symmetry | ] | |
  eapply Mem_permut; [ symmetry | rewrite Mem_app_or_eq; left ]]; eauto.
(* lam *)
apply t_lam_L with (L:=L \u used_vars_context_L (Gamma++Gamma')).
  eapply ok_L_permut; [ | symmetry | ]; eauto.
  intros; apply H with (Gamma':=Gamma'); auto; rew_app;
  [ apply ok_L_extend_fresh | permut_simpl]; auto.
(* appl *)
apply t_appl_L with (A:=A).
  eapply ok_L_permut; [ | symmetry | ]; eauto.
  apply IHtypes_L1 with (Gamma':=Gamma'); auto.
  apply IHtypes_L2 with (Gamma':=Gamma'); auto.
(* box *)
apply t_box_L with (L:=L \u from_list Omega).
  eapply ok_L_permut; [ | symmetry | ]; eauto.
  auto.
  intros; apply H with (Gamma':=Gamma'); auto.
  destruct Ok0; split; auto; simpl; split; [apply notin_Mem | ]; auto.
(* unbox *)
constructor; auto.
  eapply ok_L_permut; [ | symmetry | ]; eauto.
  apply IHtypes_L with (Gamma' := Gamma'); auto.
(* fetch *)
constructor; auto.
  eapply ok_L_permut; [ | symmetry | ]; eauto.
  apply IHtypes_L with (Gamma' := Gamma'); auto.
(* here *)
constructor; auto.
  eapply ok_L_permut; [ | symmetry | ]; eauto.
  apply IHtypes_L with (Gamma' := Gamma'); auto.
(* get *)
constructor; auto.
  eapply ok_L_permut; [ | symmetry | ]; eauto.
  apply IHtypes_L with (Gamma' := Gamma'); auto.
(* letdia *)
apply t_letd_L with (Lt := Lt \u used_vars_context_L (Gamma++Gamma'))
  (Lw := Lw \u from_list Omega) (A := A); auto.
  eapply ok_L_permut; [ | symmetry | ]; eauto.
  apply IHtypes_L with (Gamma' := Gamma'); auto.
  intros; apply H0 with (Gamma' := Gamma'); auto.
  rew_app; apply ok_L_extend_fresh; destruct Ok0.
    split; auto. simpl; split; [apply notin_Mem | ]; auto.
    auto.
  rew_app; permut_simpl; assumption.
Qed.

Lemma WeakeningOmega_L:
forall Omega Gamma M A w w'
  (H: Omega; Gamma |- M ::: A @ w)
  (Ok: ok_L (w'::Omega) Gamma),
  forall Omega',
    Omega' *=* w'::Omega ->
    Omega'; Gamma |- M ::: A @ w.
intros Omega Gamma M A w w' H; generalize dependent w'; induction H; intros.
(* hyp *)
constructor; auto.
eapply ok_L_permut with (O:=w'::Omega); [symmetry | | ]; eauto.
eapply Mem_permut; [ symmetry | ]; eauto; rewrite Mem_cons_eq; right; auto.
(* lam *)
apply t_lam_L with (L:=L \u used_vars_context_L Gamma).
eapply ok_L_permut with (O:=w'::Omega); [symmetry | | ]; eauto.
intros; eapply H; eauto.
apply ok_L_extend_fresh; destruct Ok0; auto; split; auto.
(* appl *)
apply t_appl_L with (A:=A); eauto.
eapply ok_L_permut with (O:=w'::Omega); [symmetry | | ]; eauto.
(* box *)
apply t_box_L with (L:=L \u from_list (w'::Omega)).
eapply ok_L_permut with (O:=w'::Omega); [symmetry | | ]; eauto.
eapply Mem_permut; [ symmetry | ]; eauto; rewrite Mem_cons_eq; right; auto.
intros; apply H with (w':=w'); auto.
eapply ok_L_permut with (O:=(x::w'::Omega)); eauto.
permut_simpl.
destruct Ok0; split; auto; simpl. split; auto.
apply notin_Mem; eauto.
permut_simpl; auto.
(* unbox *)
constructor; eauto.
eapply ok_L_permut with (O:=w'::Omega); [symmetry | | ]; eauto.
(* fetch *)
constructor; eauto.
eapply ok_L_permut with (O:=w'0::Omega); [symmetry | | ]; eauto.
apply Mem_permut with (l:=w'0::Omega); rew_app;
[ symmetry | rewrite Mem_cons_eq; right]; auto.
(* here *)
constructor; eauto.
eapply ok_L_permut with (O:=w'::Omega); [symmetry | | ]; eauto.
(* get *)
constructor; eauto.
eapply ok_L_permut with (O:=w'0::Omega); [symmetry | | ]; eauto.
apply Mem_permut with (l:=w'0::Omega); rew_app;
[ symmetry | rewrite Mem_cons_eq; right]; auto.
(* letd *)
apply t_letd_L with (Lt := Lt \u used_vars_context_L Gamma)
  (Lw := Lw \u from_list (w'::Omega)) (A := A).
  eapply ok_L_permut with (O:=w'::Omega); [symmetry | | ]; eauto.
  apply IHtypes_L with (w' := w'); auto.
  intros; apply H0 with (w' := w'0) (w'0 := w'); auto.
  eapply ok_L_permut with (O:=w'0::w'::Omega).
  permut_simpl. eauto.
  apply ok_L_extend_fresh; destruct Ok0.
    split; auto. simpl; split; [apply notin_Mem | ]; auto.
    auto.
  permut_simpl; assumption.
Qed.

Lemma PermutOmega_L:
forall Omega Gamma M A w Omega',
  Omega; Gamma |- M ::: A @ w ->
  Omega *=* Omega' ->
  Omega'; Gamma |- M ::: A @ w.
intros; generalize dependent Omega'; induction H; intros;
econstructor;
try (eapply ok_L_permut);
try (eapply Mem_permut); eauto.
Qed.

Lemma PermutGamma_L:
forall Omega Gamma M A w Gamma',
  Omega; Gamma |- M ::: A @ w ->
  Gamma *=* Gamma' ->
  Omega; Gamma' |- M ::: A @ w.
intros; generalize dependent Gamma'; induction H; intros;
econstructor;
try (eapply ok_L_permut);
try (eapply Mem_permut); eauto.
Qed.

Lemma subst_t_L_types_preserv:
forall Omega Gamma Gamma0 M A B w w' N x,
  lc_w_L N -> lc_t_L N ->
  Omega; Gamma |- M ::: A @ w ->
  Gamma *=*  (w', (x, B)) :: Gamma0 ->
  Omega; nil |- N ::: B @ w' ->
  forall Gamma', Gamma' *=* Gamma0 ->
  Omega; Gamma' |- [ N // fte x ] M ::: A @ w.
intros.
generalize dependent Gamma0; generalize dependent Gamma'.
induction H1; intros; simpl in *.
(* hyp *)
case_if.
inversion H1; subst.
assert ((w', (x, B)) = (w, (x, A))).
  eapply ok_L_permut with (G':=(w', (x, B))::Gamma0) in Ok; eauto.
  destruct Ok as (OkO, Ok);
  apply ok_L_Mem_contr with (w':=w) (b:=A) in Ok.
  apply Mem_permut with (l':=(w', (x, B)) :: Gamma0) in HT; auto.
  rewrite Mem_cons_eq in HT; destruct HT.
    symmetry; auto.
    contradiction.
inversion H5; subst; auto.
replace Gamma' with (nil ++ Gamma') by auto;
apply WeakeningGamma_L with (Gamma:=nil) (Gamma':=Gamma'); rew_app; auto;
eapply ok_L_permut with (G:=Gamma0); [ | symmetry | ]; eauto;
eapply ok_L_permut with (G':=(w, (x,A))::Gamma0) in Ok; eauto;
eapply ok_L_smaller_Gamma; eauto.
constructor; auto.
eapply ok_L_permut with (G':=(w', (x, B)) :: Gamma') in Ok; eauto.
apply ok_L_smaller_Gamma in Ok; auto. rewrite H4; auto.
apply Mem_permut with (l':= (w', (x, B)) :: Gamma0) in HT; eauto;
rewrite Mem_cons_eq in HT; destruct HT;
[ inversion H5; subst; elim H1 |
  symmetry in H4; apply Mem_permut with (l:=Gamma0) ]; auto.
(* lam *)
apply t_lam_L with (L:=L \u \{x}).
eapply ok_L_permut with (G':=(w', (x, B))::Gamma0) in Ok; eauto;
apply ok_L_smaller_Gamma in Ok; symmetry in H4;
eapply ok_L_permut with (G:=Gamma0); auto.
intros; unfold open_t_L in *;
rewrite <- subst_t_comm_L; auto; eapply H1; auto;
rewrite H2; rewrite H4; permut_simpl.
(* appl *)
apply t_appl_L with (A:=A).
eapply ok_L_permut with (G':=(w', (x, B))::Gamma0) in Ok; eauto;
apply ok_L_smaller_Gamma in Ok; symmetry in H4;
eapply ok_L_permut with (G:=Gamma0); auto.
eapply IHtypes_L1; auto; rewrite H2; rewrite H4; permut_simpl.
eapply IHtypes_L2; auto; rewrite H2; rewrite H4; permut_simpl.
(* box *)
apply t_box_L with (L:=L \u from_list Omega); auto.
eapply ok_L_permut with (G':=(w', (x, B))::Gamma0) in Ok; eauto;
apply ok_L_smaller_Gamma in Ok; symmetry in H4;
eapply ok_L_permut with (G:=Gamma0); auto.
intros; unfold open_w_L in *.
rewrite subst_order_irrelevant_bound_L; auto;
eapply H1; eauto. eapply WeakeningOmega_L; eauto.
destruct Ok; split; auto; constructor;
[apply notin_Mem |]; auto.
(* unbox *)
constructor.
eapply ok_L_permut with (G':=(w', (x, B))::Gamma0) in Ok; eauto;
apply ok_L_smaller_Gamma in Ok; symmetry in H4;
eapply ok_L_permut with (G:=Gamma0); auto.
eapply IHtypes_L; eauto.
(* fetch *)
constructor; eauto.
eapply ok_L_permut with (G':=(w', (x, B))::Gamma0) in Ok; eauto;
apply ok_L_smaller_Gamma in Ok; symmetry in H4;
eapply ok_L_permut with (G:=Gamma0); auto.
(* here *)
constructor; eauto.
eapply ok_L_permut with (G':=(w', (x, B))::Gamma0) in Ok; eauto;
apply ok_L_smaller_Gamma in Ok; symmetry in H4;
eapply ok_L_permut with (G:=Gamma0); auto.
(* get *)
constructor; eauto.
eapply ok_L_permut with (G':=(w', (x, B))::Gamma0) in Ok; eauto;
apply ok_L_smaller_Gamma in Ok; symmetry in H4;
eapply ok_L_permut with (G:=Gamma0); auto.
(* letd *)
apply t_letd_L with (A:=A) (Lt:=Lt \u \{x}) (Lw:=Lw \u from_list Omega).
eapply ok_L_permut with (G':=(w', (x, B))::Gamma0) in Ok; eauto;
apply ok_L_smaller_Gamma in Ok; symmetry in H5;
eapply ok_L_permut with (G:=Gamma0); auto.
eapply IHtypes_L; eauto.
intros; unfold open_t_L in *; unfold open_w_L in *.
rewrite subst_order_irrelevant_bound_L; auto;
rewrite <- subst_t_comm_L; auto; eapply H2; eauto.
eapply WeakeningOmega_L; eauto.
destruct Ok; split; simpl; auto; split; auto;
apply notin_Mem; auto.
rewrite H4; rewrite H5; permut_simpl.
Qed.

Lemma rename_w_L_types_preserv:
forall Omega Omega' Gamma M A w w0 w1 w' Gamma',
  Omega'; Gamma |- M ::: A @ w -> Mem w1 Omega ->
  w0 <> w1 ->
  w0::Omega *=* Omega' ->
  w' = (if eq_var_dec w w0 then w1 else w) ->
  Gamma' = rename_context_L w0 w1 Gamma ->
  Omega; Gamma' |- {{ fwo w1 // fwo w0 }} M ::: A @ w'.
intros;
generalize dependent w';
generalize dependent Gamma';
generalize dependent w1.
generalize dependent Omega;
generalize dependent w0.
induction H; intros; simpl in *.
(* hyp *)
case_if; try subst.
constructor; [eapply ok_L_rename | | ]; eauto.
apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
[ | symmetry | ]; auto;
destruct Ok; split; auto; simpl in *; destruct H; auto.
eapply Mem_rename_context_L; repeat case_if; eauto; elim H; eauto.
constructor; [eapply ok_L_rename | | ]; eauto.
apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
[ | symmetry | ]; auto;
destruct Ok; split; auto; simpl in *; destruct H3; auto.
apply Mem_permut with (l':=w0::Omega0) in World; [|symmetry]; auto;
rewrite Mem_cons_eq in World; destruct World; subst.
  elim H; auto. auto.
eapply Mem_rename_context_L; repeat case_if; eauto; elim H; eauto.
(* lam *)
econstructor; eauto.
subst.
eapply ok_L_rename; eauto.
apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok; try symmetry; auto;
destruct Ok; split; simpl in *; destruct H3; auto.
intros; unfold open_t_L in *; case_if; subst.
replace ((w1, (x, A)) :: rename_context_L w0 w1 Gamma) with
  (rename_context_L w0 w1 ((w0, (x, A)) :: Gamma)) by (simpl; case_if; auto).
rewrite <- subst_order_irrelevant_free_L; simpl; auto.
eapply H; simpl; try case_if; eauto.
replace ((w, (x, A)) :: rename_context_L w0 w1 Gamma) with
  (rename_context_L w0 w1 ((w, (x, A)) :: Gamma)) by (simpl; case_if; auto).
rewrite <- subst_order_irrelevant_free_L; simpl; auto.
eapply H; simpl; try case_if; eauto.
(* appl *)
econstructor; eauto; clear IHtypes_L1 IHtypes_L2.
subst; apply ok_L_rename;
apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
destruct Ok. split; simpl in *; destruct H4; auto. symmetry; auto.
auto.
(* box *)
apply t_box_L with (L:=L \u \{w0}); eauto.
subst; apply ok_L_rename;
apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok; auto.
destruct Ok. split; simpl in *; destruct H3; auto.
symmetry; auto.
case_if; subst; auto. apply Mem_permut with (l':=w0::Omega0) in World.
rewrite Mem_cons_eq in World. destruct World; subst; [elim H5 | ]; auto.
symmetry; auto.
intros; unfold open_w_L in *.
rewrite <- subst_w_comm_L; eauto.
eapply H; eauto. subst; permut_simpl.
rew_app; auto.
rewrite Mem_cons_eq; right; auto.
repeat case_if; subst; auto; rewrite notin_union in H5; destruct H5;
rewrite notin_singleton in H4; elim H4; auto.
(* unbox *)
constructor.
subst; apply ok_L_rename;
apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok; try symmetry; auto;
destruct Ok; split; simpl in *; destruct H3; auto.
eapply IHtypes_L; eauto.
(* fetch *)
repeat case_if; subst; try inversion H5; subst.
constructor; [ | eapply IHtypes_L | ]; repeat case_if; eauto;
apply ok_L_rename; apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
try symmetry; auto; destruct Ok as (OkA, OkB); split; simpl in *;
destruct OkA; auto.
constructor;
[ | eapply IHtypes_L |
  apply Mem_permut with (l':=w0::Omega0) in Hin];
repeat case_if; eauto.
apply ok_L_rename; apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
try symmetry; auto; destruct Ok as (OkA, OkB); split; simpl in *;
destruct OkA; auto.
rewrite Mem_cons_eq in Hin; destruct Hin; subst; [elim H6 | ]; auto.
symmetry; auto.
constructor; [ | eapply IHtypes_L | ]; repeat case_if; eauto;
apply ok_L_rename; apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
try symmetry; auto; destruct Ok as (OkA, OkB); split; simpl in *;
destruct OkA; auto.
constructor;
[ | eapply IHtypes_L |
  apply Mem_permut with (l':=w0::Omega0) in Hin];
repeat case_if; eauto.
apply ok_L_rename; apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
try symmetry; auto; destruct Ok as (OkA, OkB); split; simpl in *;
destruct OkA; auto.
rewrite Mem_cons_eq in Hin; destruct Hin; subst; [elim H6 | ]; auto.
symmetry; auto.
(* here *)
constructor.
subst; apply ok_L_rename;
apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok; try symmetry; auto;
destruct Ok; split; simpl in *; destruct H3; auto.
eapply IHtypes_L; eauto.
(* get *)
repeat case_if; subst; try inversion H5; subst.
constructor; [ | eapply IHtypes_L | ]; repeat case_if; eauto;
apply ok_L_rename; apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
try symmetry; auto; destruct Ok as (OkA, OkB); split; simpl in *;
destruct OkA; auto.
constructor;
[ | eapply IHtypes_L |
  apply Mem_permut with (l':=w0::Omega0) in Hin];
repeat case_if; eauto.
apply ok_L_rename; apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
try symmetry; auto; destruct Ok as (OkA, OkB); split; simpl in *;
destruct OkA; auto.
rewrite Mem_cons_eq in Hin; destruct Hin; subst; [elim H6 | ]; auto.
symmetry; auto.
constructor; [ | eapply IHtypes_L | ]; repeat case_if; eauto;
apply ok_L_rename; apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
try symmetry; auto; destruct Ok as (OkA, OkB); split; simpl in *;
destruct OkA; auto.
constructor;
[ | eapply IHtypes_L |
  apply Mem_permut with (l':=w0::Omega0) in Hin];
repeat case_if; eauto.
apply ok_L_rename; apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
try symmetry; auto; destruct Ok as (OkA, OkB); split; simpl in *;
destruct OkA; auto.
rewrite Mem_cons_eq in Hin; destruct Hin; subst; [elim H6 | ]; auto.
symmetry; auto.
(* letd *)
apply t_letd_L with (A:=A) (Lt:=Lt) (Lw:=Lw \u \{w0}).
subst; apply ok_L_rename;
apply ok_L_permut with (O':=w0::Omega0) (G':=Gamma) in Ok;
try symmetry; auto; destruct Ok as (OkA, OkB); split; simpl in *;
destruct OkA; auto.
eapply IHtypes_L; eauto.
unfold open_w_L in *; unfold open_t_L in *.
case_if; subst; intros;
replace ((w', (t, A)) :: rename_context_L w0 w1 Gamma) with
  (rename_context_L w0 w1 ((w', (t, A)) :: Gamma)) by
( simpl; rewrite notin_union in H5; destruct H5 as (H5a, H5b);
  rewrite notin_singleton in H5b; case_if; auto);
rewrite <- subst_w_comm_L; auto;
rewrite <- subst_order_irrelevant_free_L; simpl; auto;
eapply H0; try rewrite <- H2; try case_if; eauto; try permut_simpl;
rewrite Mem_cons_eq; right; auto.
Qed.

Lemma types_w_in_Omega_L:
forall Omega Gamma M A w,
  Omega; Gamma |- M ::: A @ w ->
  Mem w Omega.
intros; induction H; auto.
assert (exists x, x \notin L) by apply Fresh;
destruct H0 as (x, H0); specialize H with x;
apply H; auto.
Qed.

Lemma rename_w_types_preserv_in_new_L:
forall Omega Gamma M A w0 w1,
  w1::Omega; Gamma |- M ::: A @ w0 -> w0 <> w1 ->
  Omega; (rename_context_L w1 w0 Gamma) |- {{ fwo w0 // fwo w1 }} M ::: A @ w0.
intros; eapply rename_w_L_types_preserv with (w:=w0); eauto.
apply types_w_in_Omega_L in H; rewrite Mem_cons_eq in H; destruct H; subst;
[ elim H0 | ]; auto.
case_if; auto.
Qed.

Lemma rename_w_types_preserv_in_outer_L:
forall Omega Gamma M A w0 w1 w2,
  w1::Omega; Gamma |- M ::: A @ w2 -> w0 <> w1 -> w0 <> w2 -> w1 <> w2 ->
  Mem w0 Omega ->
  Omega; (rename_context_L w1 w0 Gamma) |- {{ fwo w0 // fwo w1 }} M ::: A @ w2.
intros; eapply rename_w_L_types_preserv; eauto.
case_if; auto.
Qed.

Lemma types_L_Mem_Omega:
forall M Omega Gamma A w,
  Omega; Gamma |- M ::: A @ w ->
  Mem w Omega.
intros; induction H; eauto;
assert (exists x, x \notin L) as H0 by apply Fresh; destruct H0 as (x);
apply H with (x:=x); auto.
Qed.

Lemma ProgressL:
forall Omega M A w
  (H_lc: lc_w_L M)
  (H_lc': lc_t_L M)
  (HProgress: Omega; nil |- M ::: A@w),
  value_L M \/ exists N, (M, fwo w) |-> (N, fwo w).
induction M; intros; eauto using value_L; inversion HProgress; subst.
(* hyp *)
rewrite Mem_nil_eq in HT; contradiction.
(* lam *)
right; inversion H_lc; inversion H_lc'; subst;
destruct (IHM1 (A0 ---> A) w H2 H7 HT1).
  inversion H; subst; inversion HT1; subst.
  inversion H2; inversion H7; subst;
  eexists; constructor; eauto. apply lc_t_subst_L; auto.
  destruct H; eexists; constructor; eauto.
(* unbox *)
right; inversion H_lc; inversion H_lc'; subst.
destruct (IHM ([*]A) w H1 H4 HT).
  inversion H; subst; inversion HT; subst.
  inversion H1; inversion H4; subst; eexists; constructor; eauto.
  apply lc_w_subst_L; auto.
  destruct H; eexists; constructor; eauto.
(* get *)
inversion H_lc; inversion H_lc'; subst.
destruct (IHM (<*>A0) w0 H1 H5 HT).
  inversion H; subst; inversion HT; subst.
  right; exists (get_L (fwo w2) (here_L M0)); apply red_get_val_L; eauto.
  destruct H as (N); right; eexists; constructor; eauto.
(*
right; inversion H_lc; inversion H_lc'; subst.
destruct (IHM (<*>A0) w0 H1 H5 HT).
  inversion H; subst; inversion HT; subst.
    inversion H1; inversion H5; subst.
    eexists; apply red_get_val_L; eauto.
  destruct H; eexists; constructor; eauto.
*)
(* letd *)
right; inversion H_lc; inversion H_lc'; subst.
destruct (IHM1 (<*>A0) w H3 H8 HT1).
  inversion H; subst; inversion HT1; subst.
  inversion H3; inversion H8; subst;
  inversion H4; inversion H10; subst;
  eexists; constructor; eauto.
  apply lc_t_subst_L; auto.
  apply lc_w_subst_L; auto.
  destruct H; eexists; constructor; eauto.
  apply lc_t_subst_L; auto.
  apply lc_w_subst_L; auto.
(* here *)
inversion H_lc; inversion H_lc'; subst.
destruct (IHM A0 w H1 H4 HT).
  right; exists (get_L (fwo w) (here_L M)); constructor; auto.
  right; destruct H; eexists; constructor; eauto.
(* fetch *)
right; inversion H_lc; inversion H_lc'; subst.
destruct (IHM ([*]A0) w0 H1 H5 HT).
  inversion H; subst; inversion HT; subst.
    inversion H1; inversion H5; subst.
    eexists; apply red_fetch_val_L; eauto.
  destruct H; eexists; constructor; eauto.
Qed.

Lemma PreservationL:
forall Omega M N A w w'
  (HType: Omega; nil |- M ::: A@w)
  (HStep: (M, fwo w) |-> (N,fwo w')),
  Omega; nil |- N ::: A@w'.
intros; remember (@nil (prod var (prod var ty))) as Gamma;
generalize dependent N; generalize dependent w';
induction HType; intros; inversion HStep; subst; eauto using types_L.
(* red_appl_lam *)
inversion HType1; subst; unfold open_t_L in *.
assert (exists x, x \notin L \u used_vars_term_L M0 \u \{w'}) as HF
  by apply Fresh.
destruct HF as (v_f).
replace ([N // bte 0] M0) with ([N // fte v_f] ([hyp_L (fte v_f) // bte 0] M0)).
eapply subst_t_L_types_preserv with (B:=A); eauto.
rewrite <- subst_t_neutral_free_L with (n:=0); auto.
(* red_unbox_box *)
inversion HType; subst; unfold open_w_L in *;
assert (exists x, x \notin L \u used_worlds_term_L M0 \u \{w'}) as HF
  by apply Fresh;
destruct HF as (w_f).
replace ({{fwo w'//bwo 0}}M0) with ({{fwo w'//fwo w_f}}{{fwo w_f//bwo 0}}M0).
replace (@nil (prod var (prod var ty))) with (rename_context_L w_f w' nil) by
  (simpl; auto).
eapply rename_w_L_types_preserv; auto. case_if; auto.
rewrite <- subst_w_neutral_free_L; auto.
(* red_fetch_val *)
inversion HVal; subst; [inversion HType | | inversion HType].
inversion HType; subst; econstructor; eauto.
(*destruct (eq_var_dec w'0 w); subst; [rewrite rename_w_same_L|]; auto;
replace (@nil (prod var (prod var ty))) with (rename_context_L w w'0 nil) by
  (simpl; auto).
assert (Mem w Omega) by (eapply types_w_in_Omega_L; eauto);
apply Mem_split in H; destruct H as (hd, (tl, H));
apply PermutOmega_L with (Omega := w :: hd ++ tl); [ | permut_simpl];
[ eapply WeakeningOmega_L | rewrite H ]; eauto; try permut_simpl.
eapply rename_w_L_types_preserv with (w:=w); try case_if; subst; eauto;
try permut_simpl.
rewrite Mem_app_or_eq;
rewrite Mem_app_or_eq in Hin; destruct Hin.
  rewrite Mem_app_or_eq in H; destruct H; [ left | rewrite Mem_cons_eq in H];
  auto; destruct H; [ subst | rewrite Mem_nil_eq in H; contradiction].
  elim n; auto.
  right; auto.
simpl; destruct Ok; split; auto; apply ok_Omega_L_permut with (O1:=Omega); auto;
rewrite H; permut_simpl.
*)
(* red_get_here *)
destruct Ok; repeat constructor; auto;
apply types_L_Mem_Omega in HType; auto.
(* red_get_val *)
inversion HType; subst; constructor; auto.
(*
replace (@nil (prod var (prod var ty))) with (rename_context_L w w'0 nil) by
  (simpl; auto).
destruct (eq_var_dec w'0 w); subst; [rewrite rename_w_same_L|]; auto;
replace (@nil (prod var (prod var ty))) with (rename_context_L w w'0 nil) by
  (simpl; auto).
assert (Mem w Omega) by (eapply types_w_in_Omega_L; eauto);
apply Mem_split in H; destruct H as (hd, (tl, H));
apply PermutOmega_L with (Omega := w :: hd ++ tl); [ | permut_simpl];
[ eapply WeakeningOmega_L | rewrite H ]; eauto; try permut_simpl.
eapply rename_w_L_types_preserv with (w:=w); try case_if; eauto.
rewrite Mem_app_or_eq;
rewrite H in Hin; rewrite Mem_app_or_eq in Hin; destruct Hin.
  rewrite Mem_app_or_eq in H0; destruct H0; [ left | rewrite Mem_cons_eq in H0];
  auto; destruct H0; [ subst | rewrite Mem_nil_eq in H0; contradiction].
  elim n; auto.
  right; auto.
subst; permut_simpl.
simpl; destruct Ok; split; auto; apply ok_Omega_L_permut with (O1:=Omega); auto;
rewrite H; permut_simpl.
*)
(* red_letd_here *)
clear H.
inversion HType; subst; unfold open_w_L in *; unfold open_t_L in *;
assert (exists x, x \notin Lt \u used_vars_term_L {{fwo w // bwo 0}}N)
  as HF by apply Fresh;
destruct HF as (v_f);
assert (exists x, x \notin Lw \u used_worlds_term_L [hyp_L (fte v_f) // bte 0]N
                           \u \{w} \u \{w'})
  as HF by apply Fresh;
destruct HF as (w_f).
replace ([M0 // bte 0] ({{fwo w // bwo 0}}N)) with
  ([M0 // fte v_f] ([hyp_L (fte v_f) // bte 0] ({{fwo w// bwo 0}} N))) by
  (rewrite <- subst_t_neutral_free_L; auto);
apply subst_t_L_types_preserv with (Gamma:=(w, (v_f, A)) :: nil)
                                     (Gamma0:=nil) (w':=w)
                                                (B:=A); eauto.
rewrite <- subst_order_irrelevant_bound_L; [ | constructor];
replace ( {{fwo w // bwo 0}}([hyp_L (fte v_f) // bte 0]N)) with
  ({{fwo w // fwo w_f}} ({{fwo w_f // bwo 0}} ([hyp_L (fte v_f) // bte 0] N)))
  by (rewrite <- subst_w_neutral_free_L; auto).
replace ((w, (v_f, A)) :: nil)
  with (rename_context_L  w_f w ((w_f, (v_f, A))::nil)) by
( simpl; repeat rewrite notin_union in H0; rewrite notin_singleton in H0;
  repeat destruct H0 as (H0a, (H0b, H0c)); case_if; auto).
destruct (eq_var_dec w w'); subst.
(* w = w' *)
eapply rename_w_types_preserv_in_new_L.
rewrite subst_order_irrelevant_bound_L; auto.
constructor.
repeat rewrite notin_used in H0; intro; repeat rewrite notin_union in H0; subst;
destruct H0; destruct H1; rewrite notin_singleton in H2; elim H2; auto.
(* <> *)
eapply rename_w_types_preserv_in_outer_L.
rewrite subst_order_irrelevant_bound_L; auto.
constructor.
repeat rewrite notin_union in H0; destruct H0; destruct H1;
rewrite notin_singleton in H2; intro; elim H2; subst; auto.
auto.
repeat rewrite notin_union in H0; destruct H0; destruct H1; destruct H2;
rewrite notin_singleton in H3; auto.
apply types_L_Mem_Omega in HT; auto.
inversion HT; auto.
Qed.
