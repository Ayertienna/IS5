Require Import LLSubstitution.
Require Import PermutLib.
Require Import LibTactics.
Require Import LLOkLib.

Open Scope is5_scope.
Open Scope labeled_is5_scope.
Open Scope permut_scope.

Global Reserved Notation " Omega ';' Gamma '|-' M ':::' A '@' w " (at level 70).

Inductive types_L: worlds_L -> Context_L -> te_L -> ty -> var -> Prop :=

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
    (x :: Omega); Gamma |- (M ^w^ (fwo x)) ::: A @ w),
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

| t_here: forall Omega Gamma w M A
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
    w' :: Omega; (w, (t, A)) :: Gamma |-
      ((N ^w^ (fwo w')) ^t^ (hyp_L (fte t)))  ::: B @ w),
  Omega; Gamma |-letd_L M N ::: B @ w

where " Omega ';' Gamma '|-' M ':::' A '@' w " := (types_L Omega Gamma M A w):
  labeled_is5_scope.

Inductive value_L: te_L -> Prop :=
| val_lam_L: forall A M, value_L (lam_L A M)
| val_box_L: forall M, value_L (box_L M)
| val_here_L: forall M (HT: value_L M), value_L (here_L M)
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
| red_letd_here_L: forall M N w (HVal: value_L M),
   lc_t_L M -> lc_w_L M ->
   lc_t_L (N ^t^ M) -> lc_w_L (N ^w^ w) ->
   (letd_L (here_L M) N, w) |-> ((N ^w^ w) ^t^ M, w)
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
   (fetch_L w M, w') |-> ({{w'//w}}M, w')
| red_here_L: forall N N' w (HRed: (N, w) |-> (N',w)),
   lc_t_L N -> lc_w_L N ->
   (here_L N, w) |-> (here_L N', w)
| red_letd_L: forall M M' N w (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   lc_t_L (N ^t^ M) -> lc_w_L (N ^w^ w) ->
   (letd_L M N, w) |-> (letd_L M' N, w)
| red_get_L: forall w M M' w' (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   (get_L w M, w') |-> (get_L w M', w')
| red_get_val_L: forall w M w' (HVal: value_L M),
   lc_t_L M -> lc_w_L M ->
   (get_L w (here_L M), w') |-> (here_L {{w'//w}}M, w')
where " M |-> N " := (step_L M N ) : labeled_is5_scope.

Lemma WeakeningGamma:
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

Lemma WeakeningOmega:
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

Lemma PermutOmega:
forall Omega Gamma M A w Omega',
  Omega; Gamma |- M ::: A @ w ->
  Omega *=* Omega' ->
  Omega'; Gamma |- M ::: A @ w.
intros; generalize dependent Omega'; induction H; intros;
econstructor;
try (eapply ok_L_permut);
try (eapply Mem_permut); eauto.
Qed.

Lemma PermutGamma:
forall Omega Gamma M A w Gamma',
  Omega; Gamma |- M ::: A @ w ->
  Gamma *=* Gamma' ->
  Omega; Gamma' |- M ::: A @ w.
intros; generalize dependent Gamma'; induction H; intros;
econstructor;
try (eapply ok_L_permut);
try (eapply Mem_permut); eauto.
Qed.

Lemma subst_t_types_preserv:
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
apply WeakeningGamma with (Gamma:=nil) (Gamma':=Gamma'); rew_app; auto;
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
rewrite <- subst_t_comm; auto; eapply H1; auto;
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
rewrite subst_order_irrelevant_bound; auto;
eapply H1; eauto. eapply WeakeningOmega; eauto.
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
rewrite subst_order_irrelevant_bound; auto;
rewrite <- subst_t_comm; auto; eapply H2; eauto.
eapply WeakeningOmega; eauto.
destruct Ok; split; simpl; auto; split; auto;
apply notin_Mem; auto.
rewrite H4; rewrite H5; permut_simpl.
Qed.

Lemma rename_w_types_preserv:
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
rewrite <- subst_order_irrelevant_free; simpl; auto.
eapply H; simpl; try case_if; eauto.
replace ((w, (x, A)) :: rename_context_L w0 w1 Gamma) with
  (rename_context_L w0 w1 ((w, (x, A)) :: Gamma)) by (simpl; case_if; auto).
rewrite <- subst_order_irrelevant_free; simpl; auto.
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
rewrite <- subst_w_comm; eauto.
eapply H; eauto. subst; permut_simpl.
rew_app; auto.
rewrite Mem_cons_eq; right; auto.
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
replace ((w1, (t, A)) :: rename_context_L w0 w1 Gamma) with
  (rename_context_L w0 w1 ((w0, (t, A)) :: Gamma)) by (simpl; case_if; auto);
rewrite <- subst_w_comm; auto;
rewrite <- subst_order_irrelevant_free; simpl; auto;
eapply H0; try rewrite <- H2; try case_if; eauto; try permut_simpl;
rewrite Mem_cons_eq; right; auto.
Qed.

Lemma types_w_in_Omega:
forall Omega Gamma M A w,
  Omega; Gamma |- M ::: A @ w ->
  Mem w Omega.
intros; induction H; auto.
assert (exists x, x \notin L) by apply Fresh;
destruct H0 as (x, H0); specialize H with x;
apply H; auto.
Qed.

Lemma rename_w_types_preserv_in_new:
forall Omega Gamma M A w0 w1,
  w1::Omega; Gamma |- M ::: A @ w0 -> w0 <> w1 ->
  Omega; (rename_context_L w1 w0 Gamma) |- {{ fwo w0 // fwo w1 }} M ::: A @ w0.
intros; eapply rename_w_types_preserv with (w:=w0); eauto.
apply types_w_in_Omega in H; rewrite Mem_cons_eq in H; destruct H; subst;
[ elim H0 | ]; auto.
case_if; auto.
Qed.

Lemma Progress:
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
  eexists; constructor; eauto. apply lc_t_subst; auto.
  destruct H; eexists; constructor; eauto.
(* unbox *)
right; inversion H_lc; inversion H_lc'; subst.
destruct (IHM ([*]A) w H1 H4 HT).
  inversion H; subst; inversion HT; subst.
  inversion H1; inversion H4; subst; eexists; constructor; eauto.
  apply lc_w_subst; auto.
  destruct H; eexists; constructor; eauto.
(* get *)
right; inversion H_lc; inversion H_lc'; subst.
destruct (IHM (<*>A0) w0 H1 H5 HT).
  inversion H; subst; inversion HT; subst.
    inversion H1; inversion H5; subst.
    eexists; apply red_get_val_L; eauto.
  destruct H; eexists; constructor; eauto.
(* letd *)
right; inversion H_lc; inversion H_lc'; subst.
destruct (IHM1 (<*>A0) w H3 H8 HT1).
  inversion H; subst; inversion HT1; subst.
  inversion H3; inversion H8; subst;
  eexists; constructor; eauto.
  apply lc_t_subst; auto.
  apply lc_w_subst; auto.
  destruct H; eexists; constructor; eauto.
  apply lc_t_subst; auto.
  apply lc_w_subst; auto.
(* here *)
inversion H_lc; inversion H_lc'; subst.
destruct (IHM A0 w H1 H4 HT).
  left; constructor; auto.
  right; destruct H; eexists; constructor; eauto.
(* fetch *)
right; inversion H_lc; inversion H_lc'; subst.
destruct (IHM ([*]A0) w0 H1 H5 HT).
  inversion H; subst; inversion HT; subst.
    inversion H1; inversion H5; subst.
    eexists; apply red_fetch_val_L; eauto.
  destruct H; eexists; constructor; eauto.
Qed.

Lemma Preservation:
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
eapply subst_t_types_preserv with (B:=A); eauto.
rewrite <- subst_t_neutral_free with (n:=0); auto.
(* red_unbox_box *)
inversion HType; subst; unfold open_w_L in *;
assert (exists x, x \notin L \u used_worlds_term_L M0 \u \{w'}) as HF
  by apply Fresh;
destruct HF as (w_f).
replace ({{fwo w'//bwo 0}}M0) with ({{fwo w'//fwo w_f}}{{fwo w_f//bwo 0}}M0).
replace (@nil (prod var (prod var ty))) with (rename_context_L w_f w' nil) by
  (simpl; auto).
apply rename_w_types_preserv_in_new; auto.
rewrite <- subst_w_neutral_free; auto.
(* red_fetch_val *)
destruct (eq_var_dec w'0 w); subst; [rewrite rename_w_same|]; auto;
replace (@nil (prod var (prod var ty))) with (rename_context_L w w'0 nil) by
  (simpl; auto).
assert (Mem w Omega) by (eapply types_w_in_Omega; eauto);
apply Mem_split in H; destruct H as (hd, (tl, H));
apply PermutOmega with (Omega := w :: hd ++ tl); [ | permut_simpl];
[ eapply WeakeningOmega | rewrite H ]; eauto; try permut_simpl.
eapply rename_w_types_preserv with (w:=w); try case_if; subst; eauto;
try permut_simpl.
rewrite Mem_app_or_eq;
rewrite Mem_app_or_eq in Hin; destruct Hin.
  rewrite Mem_app_or_eq in H; destruct H; [ left | rewrite Mem_cons_eq in H];
  auto; destruct H; [ subst | rewrite Mem_nil_eq in H; contradiction].
  elim n; auto.
  right; auto.
simpl; destruct Ok; split; auto; apply ok_Omega_permut with (O1:=Omega); auto;
rewrite H; permut_simpl.
(* red_get_here *)
inversion HType; subst; constructor; auto;
replace (@nil (prod var (prod var ty))) with (rename_context_L w w'0 nil) by
  (simpl; auto).
destruct (eq_var_dec w'0 w); subst; [rewrite rename_w_same|]; auto;
replace (@nil (prod var (prod var ty))) with (rename_context_L w w'0 nil) by
  (simpl; auto).
assert (Mem w Omega) by (eapply types_w_in_Omega; eauto);
apply Mem_split in H; destruct H as (hd, (tl, H));
apply PermutOmega with (Omega := w :: hd ++ tl); [ | permut_simpl];
[ eapply WeakeningOmega | rewrite H ]; eauto; try permut_simpl.
eapply rename_w_types_preserv with (w:=w); try case_if; eauto.
rewrite Mem_app_or_eq;
rewrite H in Hin; rewrite Mem_app_or_eq in Hin; destruct Hin.
  rewrite Mem_app_or_eq in H0; destruct H0; [ left | rewrite Mem_cons_eq in H0];
  auto; destruct H0; [ subst | rewrite Mem_nil_eq in H0; contradiction].
  elim n; auto.
  right; auto.
subst; permut_simpl.
simpl; destruct Ok; split; auto; apply ok_Omega_permut with (O1:=Omega); auto;
rewrite H; permut_simpl.
(* red_letd_here *)
clear H.
inversion HType; subst; unfold open_w_L in *; unfold open_t_L in *;
assert (exists x, x \notin Lt \u used_vars_term_L {{fwo w' // bwo 0}}N)
  as HF by apply Fresh;
destruct HF as (v_f).
assert (exists x, x \notin Lw \u used_worlds_term_L [hyp_L (fte v_f) // bte 0]N
                           \u \{w'})
  as HF by apply Fresh;
destruct HF as (w_f).
replace ([M0 // bte 0] ({{fwo w' // bwo 0}}N)) with
  ([M0 // fte v_f] ([hyp_L (fte v_f) // bte 0] ({{fwo w'// bwo 0}} N)))
  by (rewrite <- subst_t_neutral_free; auto).
eapply subst_t_types_preserv with (B:=A); eauto.
rewrite <- subst_order_irrelevant_bound; [ | constructor];
replace ( {{fwo w' // bwo 0}}([hyp_L (fte v_f) // bte 0]N)) with
  ({{fwo w' // fwo w_f}} ({{fwo w_f // bwo 0}} ([hyp_L (fte v_f) // bte 0] N)))
  by (rewrite <- subst_w_neutral_free; auto).
replace ((w', (v_f, A)) :: nil)
  with (rename_context_L  w_f w' ((w', (v_f, A))::nil)).
apply rename_w_types_preserv_in_new; auto.
rewrite subst_order_irrelevant_bound; auto; constructor.
simpl; case_if; auto.
Qed.