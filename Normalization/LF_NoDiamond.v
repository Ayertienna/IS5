Add LoadPath "..".
Add LoadPath "../LabelFree/SingleUnbox/NoDiamond".
Require Import Shared.
Require Import LabelFreeNoDia.

Open Scope is5_scope.
Open Scope permut_scope.

Definition normal_form (M: te_LF) := value_LF M.

Inductive neutral_LF: te_LF -> Prop :=
| nHyp: forall n, neutral_LF (hyp_LF n)
| nAppl: forall M N, neutral_LF (appl_LF M N)
| nUnbox: forall M, neutral_LF (unbox_LF M)
.

Lemma value_no_step:
forall M,
  value_LF M ->
  forall N , ~ M |-> N.
induction M; intros; intro;
try inversion H; inversion H0; subst;
eapply IHM; eauto.
Qed.

Lemma neutral_or_value:
forall M,
  neutral_LF M \/ value_LF M.
induction M; intros;
try (destruct IHM; [left | right]; constructor; auto);
try (left; constructor);
right;
constructor.
Qed.

Inductive SN: te_LF -> Prop :=
| val_SN: forall M, value_LF M -> SN M
| step_SN: forall M,
             (forall N, M |-> N -> SN N) ->
             SN M.


Fixpoint Red (M: te_LF) (A: ty) : Prop :=
match A with
| tvar => SN M
| tarrow A1 A2 =>
    forall N
           (H_lc: lc_t_LF N)
           (HRed: Red N A1),
      Red (appl_LF M N) A2
| tbox A1 => Red (unbox_LF M) A1
end.

Lemma closed_t_succ_LF:
forall M n,
  lc_t_n_LF n M -> lc_t_n_LF (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_LF.
Qed.

Lemma lc_t_subst_t_LF_bound:
forall M N n,
  lc_t_n_LF n N ->
  lc_t_n_LF (S n) M ->
  lc_t_n_LF n ([N//bte n] M).
induction M; intros; simpl in *; inversion H0; subst; repeat case_if;
try constructor; eauto.
assert (n <> v0) by (intro; subst; elim H1; auto); omega.
eapply IHM; auto; apply closed_t_succ_LF; auto.
Qed.

Lemma lc_t_subst_t_LF_free:
forall M N n v,
  lc_t_n_LF n N ->
  lc_t_n_LF n M ->
  lc_t_n_LF n ([N//fte v] M).
induction M; intros; simpl in *; inversion H0; subst; repeat case_if;
try constructor; eauto.
eapply IHM; eauto; apply closed_t_succ_LF; auto.
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

Lemma SN_appl:
forall M N,
  lc_t_LF (appl_LF M N) ->
  SN (appl_LF M N) ->
  SN M.
intros;
remember (appl_LF M N) as T;
generalize dependent M;
generalize dependent N;
induction H0; intros; subst;
[ inversion H0 |
  assert (neutral_LF M0 \/ value_LF M0) by apply neutral_or_value];
destruct H2;
[ inversion H; subst |
  constructor; auto];
apply step_SN; intros;
apply H1 with (N0:=appl_LF N0 N) (N:=N).
constructor; eauto.
apply lc_t_step_LF with (M:=appl_LF M0 N); auto; constructor; auto.
auto.
Qed.

Lemma SN_box:
forall M,
  lc_t_LF (unbox_LF M) ->
  SN (unbox_LF M) ->
  SN M.
intros; remember (unbox_LF M) as T;
generalize dependent M;
induction H0; intros; subst;
[ inversion H0 |
  assert (neutral_LF M0 \/ value_LF M0) by apply neutral_or_value];
destruct H2; [ inversion H; subst | constructor; auto];
apply step_SN; intros;
apply H1 with (N := unbox_LF N).
constructor; inversion H; auto.
apply lc_t_step_LF with (M:=unbox_LF M0); auto; constructor; auto.
auto.
Qed.

(* CR 2 *)
Theorem property_2:
forall A M M'
  (HRed: Red M A)
  (H_lc_t: lc_t_LF M)
  (HStep: M |-> M'),
  Red M' A.
induction A; intros; simpl in *; intros.
(* base type *)
inversion HRed; subst;
[apply value_no_step with (N:=M') in H; contradiction | apply H; auto].
(* arrow type *)
apply IHA2 with (M:=appl_LF M N); auto.
constructor; auto.
constructor; auto.
(* box type *)
apply IHA with (M:=unbox_LF M); auto; constructor; eauto.
Qed.

(* CR 3 *)
Theorem property_3:
forall A M
  (H_lc: lc_t_LF M),
  neutral_LF M ->
  (forall M', M |-> M' ->
    Red M' A) ->
   Red M A.
induction A; intros; simpl in *.
(* base type *)
intros; apply step_SN; auto.
(* arrow type *)
intros. apply IHA2; try constructor; auto; intros; simpl in *.
inversion H1; subst; inversion H; subst; eapply H0; eauto.
(* box type *)
intros; apply IHA; try constructor; auto; intros;
inversion H1; subst; [inversion H | ]; apply H0; auto.
Qed.

(* CR 1 *)
Theorem property_1:
forall A M
  (H_lc_t: lc_t_LF M),
  Red M A -> SN M.
assert (exists (x:var), x \notin \{}) as nn by apply Fresh; destruct nn; auto;
induction A; intros; simpl in *.
(* base type *)
auto.
(* arrow type *)
(* Create variable of type A1 *)
assert (forall x, nil |= (x, A1) :: nil |- hyp_LF (fte x) ::: A1).
intros; constructor.
unfold ok_Bg_LF; rew_concat; constructor;
[rewrite Mem_nil_eq | constructor]; auto.
apply Mem_here.
assert (forall x, neutral_LF (hyp_LF x)) by (intros; constructor).
assert (forall x, SN (hyp_LF x))
  by (intros; apply step_SN; intros; inversion H3).
assert (forall x, Red (hyp_LF (fte x)) A1).
  intros; apply property_3; auto.
  constructor.
  intros; inversion H4.
assert (forall x, Red (appl_LF M (hyp_LF (fte x))) A2).
intros; apply H0; auto; simpl; constructor.
assert (forall x, SN (appl_LF M (hyp_LF (fte x)))).
intros; eapply IHA2; eauto.
constructor; auto; constructor.
(* From strong_norm (appl_L M (hyp_L x)) w deduce strong_norm M w *)
eapply SN_appl; auto; constructor; auto; constructor.
(* box type *)
intros; apply SN_box.
constructor; auto.
apply IHA; [constructor | ]; auto.
Grab Existential Variables.
auto.
Qed.

Lemma reducible_abstraction:
forall A N B
  (lc_N: lc_t_LF (lam_LF A N))
  (HT: forall M,
    lc_t_LF M ->
    Red M A ->
    Red ([M// bte 0] N) B),
  Red (lam_LF A N) (A ---> B).
simpl; intros;
apply property_3;
repeat constructor; auto.
inversion lc_N; auto.
intros; inversion H; subst.
apply HT; auto.
inversion H5.
Qed.

Lemma reducible_box:
forall A M
  (lc_M: lc_t_LF M)
  (HT: Red M A),
  Red (box_LF M) ([*]A).
simpl; intros;
apply property_3;
repeat constructor; auto.
intros; inversion H; subst; auto.
inversion H2.
Qed.

Fixpoint find_var (L: list (var * ty * te_LF)) (x:var) :
                     option (var * ty * te_LF) :=
match L with
| nil => None
| (v, A, M) :: L' =>
  if (eq_var_dec x v) then Some (v, A, M) else find_var L' x
end.

Fixpoint SL (L: list (var * ty * te_LF)) M :=
match M with
| hyp_LF (bte v) => M
| hyp_LF (fte v) =>
  let x := find_var L v in
  match x with
    | Some (v, A, M) => M
    | None => hyp_LF (fte v)
  end
| lam_LF A M => lam_LF A (SL L M)
| appl_LF M N => appl_LF (SL L M) (SL L N)
| box_LF M => box_LF (SL L M)
| unbox_LF M => unbox_LF (SL L M)
end.

Lemma SL_lam:
forall L M A,
  SL L (lam_LF A M) = lam_LF A (SL L M).
induction L; intros; simpl in *; auto; destruct a; destruct p;
rewrite IHL; auto.
Qed.

Lemma SL_appl:
forall L M N,
  SL L (appl_LF M N) = appl_LF (SL L M) (SL L N).
induction L; intros; simpl in *; auto; destruct a; destruct p;
rewrite IHL; auto.
Qed.

Lemma SL_box:
forall L M,
  SL L (box_LF M) = box_LF (SL L M).
induction L; intros; simpl in *; auto; destruct a; destruct p;
rewrite IHL; auto.
Qed.

Lemma SL_unbox:
forall L M,
  SL L (unbox_LF M) = unbox_LF (SL L M).
induction L; intros; simpl in *; auto; destruct a; destruct p;
rewrite IHL; auto.
Qed.

Lemma SL_hyp:
forall L G Gamma v A,
  concat (Gamma::G) *=* map fst_ L ->
  (forall a b c, Mem (a, b, c) L -> Red c b) ->
  G |= Gamma |- hyp_LF (fte v) ::: A ->
  Red (SL L (hyp_LF (fte v))) A.
induction L; intros; rew_map in *.
symmetry in H; apply permut_nil_eq in H; rew_concat in *;
symmetry in H; apply nil_eq_app_inv in H; destruct H; subst;
inversion H1; subst; rewrite Mem_nil_eq in *; contradiction.
destruct a; destruct p; inversion H1; subst; simpl in *.
case_if.
assert (A = t0).
  (* from H and H5 *) skip.
subst; apply H0 with v0; apply Mem_here.
assert (concat (Gamma :: G) *=* (v0, t0) :: map fst_ L) by auto;
symmetry in H; apply permut_split_head in H;
destruct H as (hd, (tl, H)).
assert (exists Gamma' G', concat (Gamma :: G) *=*
                                 (v0,t0) :: concat (Gamma' :: G')).
skip.
destruct H4 as (Gamma', (G', H4)).
apply IHL with G' Gamma'.
apply permut_cons_inv with (a:=(v0,t0)).
rewrite <- H4. rewrite H3; auto.
intros. apply H0 with a; rewrite Mem_cons_eq; right; auto.
skip (* v <> v0 + H5 *).
Qed.

Lemma lc_SL:
forall L M n,
  lc_t_n_LF n M ->
  (forall a b c, Mem (a,b,c) L -> lc_t_LF c) ->
  lc_t_n_LF n (SL L M).
Admitted.

Lemma SL_subst_bte:
forall L M C k,
  [C//bte k] (SL L M) = SL L ([C // bte k] M).
Admitted.

Theorem main_theorem:
forall G Gamma M A,
  lc_t_LF M ->
  G |= Gamma |- M ::: A ->
  forall L,
    concat(Gamma::G) *=* map fst_ L ->
    (forall a b c, Mem (a,b,c) L -> lc_t_LF c) ->
    (forall a b c, Mem (a,b,c) L -> Red c b) ->
    Red (SL L M) A.
intros G Gamma M A LC HT; induction HT; intros.
(* hyp *)
apply SL_hyp with G Gamma; auto; constructor; auto.
(* lam *)
unfold open_LF in *.
assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M)) by apply Fresh.
destruct H4.
assert (forall V, Red V A -> lc_t_LF V ->
           Red (SL ((x, A, V) :: L0) [hyp_LF (fte x) // bte 0]M) B).
intros; apply H0; auto.
apply lc_t_subst_t_LF_bound; [ constructor | inversion LC]; auto.
rew_map in *; simpl; rewrite <-  H1; rew_concat; auto.
intros; rewrite Mem_cons_eq in *; destruct H7.
inversion H7; subst; auto.
apply H2 with a b; auto.
intros; rewrite Mem_cons_eq in *; destruct H7.
inversion H7; subst; auto.
apply H3 with a ; auto.
rewrite SL_lam. apply reducible_abstraction.
constructor; apply lc_SL; auto; inversion LC; auto.
intros; rewrite subst_t_neutral_free_LF with (v:=x); auto.
rewrite SL_subst_bte.
(* x is free in all L0 terms, so if it is substituted then it's only in
[x/0]M itself  - make that into a lemma *)
replace ([M0 // fte x](SL L0 [hyp_LF (fte x) // bte 0]M)) with
  (SL ((x, A, M0)::L0) [hyp_LF (fte x) // bte 0]M) by skip.
apply H5; auto.
(* appl *)
simpl in *;
inversion LC; subst; apply IHHT1; auto. apply lc_SL; auto.
(* box *)
simpl in *.
inversion LC; subst; apply property_3.
constructor; constructor; apply lc_SL; auto.
constructor.
intros; inversion H2; subst.
apply IHHT; auto; rew_concat in *; rewrite <- H; permut_simpl.
inversion H6.
(* unbox *)
simpl in *;
inversion LC; subst; apply IHHT; auto.
(* unbox-fetch *)
simpl in *;
inversion LC; subst; apply IHHT; auto;
rewrite <- H0; apply PPermut_concat_permut; rewrite <- H; PPermut_LF_simpl.
Qed.


(*
Focus 4.
inversion LC; subst; rewrite SL_unbox; apply IHHT; auto.
Focus 4.
inversion LC; subst; rewrite SL_unbox; apply IHHT; auto;
rewrite <- H0; apply PPermut_concat_permut; rewrite <- H; PPermut_LF_simpl.
Focus 3.
inversion LC; subst; rewrite SL_box; apply property_3.
constructor; constructor; apply lc_SL; auto.
constructor.
intros; inversion H3; subst.
apply IHHT; auto; rew_concat in *; rewrite <- H; permut_simpl.
inversion H7.
Focus 2.
inversion LC; subst; intros; rewrite SL_lam; apply property_3.
constructor; auto; constructor; apply lc_SL; auto.
constructor.
intros; inversion H5; subst.
Focus 2. inversion H12.
assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M)) by apply Fresh.
destruct H6.
rewrite subst_t_neutral_free_LF with (v:=x); auto.
rewrite SL_subst_bte.
replace ([N // fte x](SL L0 [hyp_LF (fte x) // bte 0]M)) with
(SL ((x, A, N)::L0) ([hyp_LF (fte x) // bte 0]M)) by (simpl; auto).
apply H0; auto. skip. rew_map; rewrite <- H1; simpl; rew_concat; auto.
intros; rewrite Mem_cons_eq in *; destruct H8.
inversion H8; subst.

Lemma SL'_appl:
forall M N L,
  Red (SL' L (appl_LF M N))
(* hyp *)
destruct (SL_hyp L G Gamma v A); auto.
constructor; auto.
rewrite H3; simpl; case_if; apply H2 with (a:=v).
apply Mem_PrepSL with (M:=hyp_LF (fte v)); rewrite H3; apply Mem_here.
(* lam *)
intros; subst; rewrite SL_lam; apply property_3.
constructor; auto. constructor. skip.
constructor.
intros. inversion H4; subst.
skip.
inversion H10.
(* appl *)
rewrite SL_appl.
simpl in *.





















































(*
(***************************************************)
Fixpoint SL (L: list (var * ty * te_LF)) (M: te_LF) : te_LF :=
match L with
| nil => M
| (v, A, C) :: L' => [C // fte v](SL L' M)
end.


Lemma nonOcc_SL:
forall L2 L1 M,
  (forall v,
     v \in used_vars_te_LF M -> ~ Mem v (map fst_ (map fst_ L2))) ->
  SL L1 (SL L2 M) = SL L1 M.
induction L2; intros; simpl in *; auto.
destruct a; destruct p.
rew_map in *; simpl in *.
replace (SL L1 [ t// fte v] (SL L2 M)) with
  (SL (L1 & (v, tvar, t)) (SL L2 M)).
rewrite IHL2.
rewrite SL_L_app; simpl.
rewrite closed_subst_t_free_LF; auto.
intro; specialize H with v; apply H in H0; elim H0; apply Mem_here.
intros; intro; elim H with (v0:=v0); auto; rew_map in *; simpl in *;
rewrite Mem_cons_eq; right; auto.
rewrite <- SL_L_app.
replace ([t // fte v](SL L2 M)) with (SL ((v, tvar, t)::L2) M)
                                      by (simpl; auto).
symmetry; rewrite <- SL_L_app.
rew_app; auto.
Qed.

Fixpoint Lc_t_L (L: list (var * ty * te_LF)) :=
match L with
| nil => True
| (v, A, C) :: L' => lc_t_LF C /\ Lc_t_L L'
end.

Lemma SL_subst_bte:
forall L M v k,
  Lc_t_L L ->
  (forall v' C A, Mem (v', A, C) L -> v' <> v) ->
  [hyp_LF (fte v) // bte k] (SL L M) = SL L ([hyp_LF (fte v) // bte k] M).
induction L; intros; simpl in *; auto;
destruct a; destruct p; destruct H;
rewrite <- subst_t_comm_LF.
rewrite IHL; auto.
intros; apply H0 with (C:=C) (A:=A); rewrite Mem_cons_eq; right; auto.
auto.
apply H0 with (C:=t) (A:=t0); apply Mem_here.
Qed.

(* All the terms are reducible *)
Fixpoint RedL (L: list (var * ty * te_LF)) : Prop :=
match L with
| nil => True
| (v, A, C) :: L' => Red C A /\ RedL L'
end.

(* Capture AT LEAS variables from M -- and with good types *)
Definition GoodL (L: list (var * ty * te_LF)) (M: te_LF) (G: bg_LF) :=
  forall v,
    v \in used_vars_te_LF M ->
    forall A,
      Mem (v, A) (concat G) ->
    Mem (v, A) (map fst_ L).

(* Capture ONLY variables from M *)
Definition NotBadL (L:list (var*ty*te_LF)) (M: te_LF) :=
  forall v A N,
    Mem (v, A, N) L ->
    v \in used_vars_te_LF M.

(* Variable repetition -- not going to happen *)
Inductive OkL: list (var * ty * te_LF) -> Prop :=
| OkLNil: OkL (@nil (var * ty * te_LF))
| OkLCons:
    forall L v A C, OkL L ->
                    ~ Mem v (map fst_ (map fst_ L)) ->
                    OkL ((v, A, C) :: L)
.

Lemma Mem_map_map:
forall L (v:var) (A: ty),
  Mem (v, A) L ->
  Mem v (map fst_ L).
induction L; intros; simpl in *.
rewrite Mem_nil_eq in H; contradiction.
destruct a; rew_map; rewrite Mem_cons_eq in H; destruct H.
inversion H; subst; simpl; apply Mem_here.
simpl; rewrite Mem_cons_eq; right; eauto.
Qed.

Lemma lc_t_n_LF_subst_t:
forall N M n,
lc_t_n_LF n M ->
lc_t_n_LF n (subst_t_LF M (bte n) N) ->
lc_t_n_LF (S n) N.
induction N; intros; simpl in *; try destruct v; constructor;
repeat case_if; try inversion H1; subst; try omega;
inversion H0; subst; eauto.
apply IHN with (M:=M); eauto; apply closed_t_succ_LF; auto.
Qed.

Lemma types_LF_lc_t_LF:
forall G Gamma M A,
  G |= Gamma |- M ::: A -> lc_t_LF M.
intros; induction H; constructor; try apply IHHT;
unfold open_LF in *; auto.
assert (exists x, x \notin L) by apply Fresh; destruct H1;
assert (x \notin L) by auto;
specialize H0 with x; apply H0 in H1;
apply lc_t_n_LF_subst_t in H0; auto; constructor.
Qed.

Lemma RedL_split:
forall L1 L2,
  RedL (L1++L2) <-> RedL L1 /\ RedL L2.
induction L1; split; intros; simpl in *; rew_app in *;
[ split; auto | destruct H; auto | |];
destruct a; destruct p; destruct H.
assert (RedL L1 /\ RedL L2) by (eapply IHL1; eauto).
destruct H1; repeat split; auto.
destruct H; split; auto; eapply IHL1; split; auto.
Qed.

Lemma Mem_fst_exists:
forall (L: list (var * ty * te_LF)) v A,
  Mem (v, A) (map fst_ L) ->
  exists N, Mem (v, A, N) L.
induction L;
intros; rew_map in *; [rewrite Mem_nil_eq in *; contradiction | destruct a];
simpl in *; destruct p; rewrite Mem_cons_eq in H; destruct H;
[inversion H; subst; exists t; apply Mem_here | apply IHL in H; destruct H];
exists x; rewrite Mem_cons_eq; right; auto.
Qed.

Lemma Red_SL_hyp:
forall L v A,
  RedL L ->
  OkL L ->
  NotBadL L (hyp_LF (fte v)) ->
  Mem (v, A) (map fst_ L) ->
  Red (SL L (hyp_LF (fte v))) A.
induction L; intros; simpl in *; unfold NotBadL in *; rew_map in *.
rewrite Mem_nil_eq in H2; contradiction.
destruct a; destruct p; simpl in *; destruct H.
inversion H0; subst.
destruct L.
rew_map in *; simpl; rewrite Mem_cons_eq in H2; destruct H2;
[inversion H2; subst | rewrite Mem_nil_eq in H2; contradiction];
case_if; auto.
(* this should lead to contradiction - L should be empty *)
destruct p; destruct p.
assert (v0 = v).
  specialize H1 with (v2:=v0)(A:=t0)(N:=t).
  rewrite <- in_singleton; apply H1; apply Mem_here.
assert (v1 = v).
  specialize H1 with (v2:=v1)(A:=t2)(N:=t1).
  rewrite <- in_singleton; apply H1; rewrite Mem_cons_eq; right; apply Mem_here.
subst; rew_map in *; simpl in *.
elim H9; apply Mem_here.
Qed.

Lemma SL_lc_t_LF:
forall L M,
  Lc_t_L L ->
  lc_t_LF M ->
  lc_t_LF (SL L M).
induction L; intros; simpl in *; auto;
destruct a; destruct p; destruct H;
apply lc_t_subst_t_LF_free; eauto; eapply IHL; eauto.
Qed.

Lemma Var_free_from_List:
forall L0 (v:var),
  ~Mem v (map fst_ (map fst_ L0)) ->
  (forall v' (C: te_LF) (A0: ty), Mem (v', A0, C) L0 -> v' <> v).
induction L0; intros; simpl.
rewrite Mem_nil_eq in H0; contradiction.
destruct a; destruct p; rewrite Mem_cons_eq in H0; destruct H0.
rew_map in *; simpl in *; inversion H0; subst.
rewrite Mem_cons_eq in H; intro; destruct H; left; subst; auto.
eapply IHL0; eauto; intro; rew_map in *; simpl in *; elim H;
rewrite Mem_cons_eq; right; auto.
Qed.

Lemma used_vars_te_LF_open_hyp:
forall M v0 v k,
  v0 <> v ->
  v0 \in used_vars_te_LF [hyp_LF (fte v) // bte k] M ->
  v0 \in used_vars_te_LF M.
induction M; intros; simpl in *; repeat case_if; simpl in *.
elim H; subst; rewrite in_singleton in H0; subst; auto.
destruct v; simpl in *; auto.
eapply IHM with (v:=v) (k:=S k); auto.
rewrite in_union in *; destruct H0;
[left; eapply IHM1 | right; eapply IHM2]; eauto.
eapply IHM; eauto.
eapply IHM; eauto.
Qed.

Lemma SN_subst:
forall M C v,
  SN M ->
  SN C ->
  SN ([C//fte v]M).
intros; generalize dependent C; generalize dependent v.
induction H; intros.
Lemma subst_value:
forall M C v,
  value_LF M -> value_LF [C//v]M.
induction M; intros; simpl in *; inversion H; subst; auto; constructor.
Qed.
simpl; constructor; apply subst_value; auto.
apply step_SN; intros.

Lemma step_subst:
forall M C C' v N,
  lc_t_LF M ->
  [C//fte v]M |-> [C//fte v]N \/
  [C//fte v]M |-> [C'//fte v]M.
induction M; intros; simpl in *; repeat case_if.


Lemma subst_red_red_subst:
forall A B M C v,
  lc_t_LF C ->
  Red M A ->
  Red C B ->
  Red ([C//fte v]M) A.
induction A; simpl; intros.
apply property_1 in H1; auto.


Theorem SL_types_reducible:
forall M G Gamma A,
  G |= Gamma |- M ::: A ->
  forall L,
    OkL L -> RedL L -> GoodL L M (Gamma::G) -> NotBadL L M ->
    Lc_t_L L -> Red (SL L M) A.
intros M G Gamma A H; induction H; intros; unfold GoodL in *.
(* hyp *)
apply Red_SL_hyp; auto. apply H2; simpl; auto;
[rewrite in_singleton | rew_concat ];
auto; rewrite Mem_app_or_eq; left; auto.
(* lam *)
assert (exists v, v \notin L \u from_list (map fst_ (concat (Gamma::G))) \u
                    used_vars_te_LF M \u
                    used_vars_te_LF (SL L0 M) \u
       from_list (map fst_ (map fst_ L0)))
  as HF by apply Fresh; destruct HF as (v);
rewrite SL_lam; apply reducible_abstraction.
rewrite <- SL_lam; apply SL_lc_t_LF; auto;
specialize H with v; apply types_LF_lc_t_LF in H; eauto;
unfold open_LF in *; constructor;
apply lc_t_n_LF_subst_t in H; auto; constructor.
intros.
Import Arith.
Fixpoint contains_bte_k (M: te_LF)(k: nat): Prop :=
match M with
| hyp_LF (bte n) => if (eq_nat_dec n k) then True else False
| hyp_LF (fte v) => False
| lam_LF A M' => contains_bte_k M' (S k)
| appl_LF M' N' => contains_bte_k M' k \/ contains_bte_k N' k
| box_LF M' => contains_bte_k M' k
| unbox_LF M' => contains_bte_k M' k
end.
Lemma contains_bte_dec:
forall M k,
  { contains_bte_k M k} + {~ contains_bte_k M k}.
induction M; intros.
induction v; simpl; [destruct (eq_nat_dec n k); auto | right; tauto].
specialize IHM with (S k); destruct IHM; simpl; auto.
specialize IHM1 with k; specialize IHM2 with k; simpl in *;
destruct IHM1; destruct IHM2; auto; try tauto.
specialize IHM with k; destruct IHM; simpl; auto.
specialize IHM with k; destruct IHM; simpl; auto.
Qed.
simpl.
destruct (contains_bte_dec M 0).
rewrite subst_t_neutral_free_LF with (v:=v); auto.
rewrite SL_subst_bte; auto.
Focus 2.
eapply Var_free_from_List; apply notin_Mem; eauto.
replace ([M0 // fte v](SL L0 [hyp_LF (fte v) // bte 0]M))
  with (SL ((v, A, M0) :: L0) [hyp_LF (fte v) // bte 0]M)
  by (simpl; auto); unfold open_LF in *.
apply H0; simpl; try split; eauto.
constructor; eauto; apply notin_Mem; eauto.
intros; rew_map in *; rew_concat in *; simpl.
destruct (eq_var_dec v0 v).
subst; rewrite Mem_cons_eq in *; destruct H11.
left; auto.
repeat rewrite notin_union in H6; destruct H6; destruct H12;
destruct H13; destruct H14.
apply notin_Mem in H12.
Lemma Mem_map_fst:
forall A B L (v:A) (w:B),
  Mem (v, w) L ->
  Mem v (map fst_ L).
induction L; intros; simpl in *.
rewrite Mem_nil_eq in H; contradiction.
destruct a; rew_map; simpl; rewrite Mem_cons_eq in *;
destruct H; [inversion H; subst |]; [left | right]; auto.
eapply IHL; eauto.
Qed.
simpl.
apply Mem_map_fst in H11; elim H12; auto.
subst; rewrite Mem_cons_eq in *; destruct H11.
inversion H11; subst; elim n; auto.
right; apply H3; simpl; auto.
apply used_vars_te_LF_open_hyp in H10; auto.
unfold NotBadL in *; intros.
rewrite  Mem_cons_eq in *; destruct H10.
inversion H10; subst.
Lemma opening_used_vars_contains:
forall M v k,
  contains_bte_k M k ->
  v \in used_vars_te_LF [hyp_LF (fte v) // bte k] M.
induction M; intros; simpl in *; repeat case_if; simpl; eauto.
rewrite in_singleton; auto.
destruct v; simpl in *; repeat case_if; try contradiction.
destruct H; rewrite in_union; [left| right]; eauto.
Qed.
apply opening_used_vars_contains; auto.
simpl in *.
Lemma used_vars_subst:
forall M N k v,
  v \in used_vars_te_LF M ->
  v \in used_vars_te_LF [N // bte k] M.
induction M; intros; simpl in *; repeat case_if; auto.
rewrite in_empty in H; contradiction.
rewrite in_union in *; destruct H; [left|right];auto.
Qed.
apply used_vars_subst; eapply H4; eauto.
(* when M does not contain bte 0 *)
assert (lc_t_LF (SL L0 M)).
apply SL_lc_t_LF; auto.
Lemma lc_t_contains_bte:
forall M k,
  lc_t_n_LF (S k) M ->
  ~ contains_bte_k M k ->
  lc_t_n_LF k M.
induction M; intros; simpl in *; repeat case_if; try destruct v;
constructor.
case_if; [elim H0 | ]; auto. inversion H; subst; omega.
inversion H; apply IHM; auto.
inversion H; apply IHM1; auto.
inversion H; apply IHM2; auto.
inversion H; apply IHM; auto.
inversion H; apply IHM; auto.
Qed.
apply lc_t_contains_bte; auto.
assert (lc_t_LF (lam_LF A M)).
  apply types_LF_lc_t_LF with (G:=G) (Gamma:=Gamma)(A:=A ---> B).
  eapply t_lam_LF; eauto.
inversion H10; subst; auto.
rewrite closed_subst_t_bound_LF with (n:=0); auto.
unfold open_LF in *.
clear dependent M0.
assert (exists x, x \notin L \u used_vars_te_LF M) by apply Fresh; destruct H7.
rewrite <- closed_subst_t_bound_LF with (v0:=0)(N:=M)(M:=hyp_LF (fte x))(n:=0);
auto.
Focus 2.
apply lc_t_contains_bte; auto.
assert (lc_t_LF (lam_LF A M)).
  apply types_LF_lc_t_LF with (G:=G) (Gamma:=Gamma)(A:=A ---> B).
  eapply t_lam_LF; eauto.
inversion H8; subst; auto.
assert (lc_t_LF M).
apply lc_t_contains_bte; auto.
assert (lc_t_LF (lam_LF A M)).
  apply types_LF_lc_t_LF with (G:=G) (Gamma:=Gamma)(A:=A ---> B).
  eapply t_lam_LF; eauto.
inversion H8; subst; auto.
apply H0; auto.
rewrite closed_subst_t_bound_LF with (n:=0); auto; intros.
apply H3; simpl; auto.
rew_concat in H11; rewrite Mem_cons_eq in H11; destruct H11; auto;
inversion H11; subst; rewrite notin_union in H7; destruct H7; contradiction.
unfold NotBadL in *; intros.
rewrite closed_subst_t_bound_LF with (n:=0); auto; intros. simpl in *;
eapply H4; eauto.
(* appl *)
unfold NotBadL in *; simpl in *.
Lemma NotBadL_appl_split1:
forall L M N
   (NotBad: ∀ (v : var) (A : ty) (N0 : te_LF),
       Mem (v, A, N0) L → v \in used_vars_te_LF M \u used_vars_te_LF N),
  exists L1,
    (forall e, Mem e L1 -> Mem e L) /\
    NotBadL L1 M.
induction L; intros.
exists (@nil (var * ty * te_LF)); split.
auto.
unfold NotBadL; intros; rewrite Mem_nil_eq in H; contradiction.
destruct (IHL M N).
intros; apply NotBad with A N0; rewrite Mem_cons_eq; right; auto.
destruct H; destruct a; destruct p;
specialize NotBad with v t0 t; rewrite in_union in NotBad.
destruct NotBad; [apply Mem_here | exists ((v,t0,t)::x) | exists x];
split; auto.
intros. rewrite Mem_cons_eq in *; destruct H2; [left | right]; auto.
unfold NotBadL in *; intros; rewrite Mem_cons_eq in *; destruct H2;
[inversion H2; subst | apply H0 in H2]; auto.
intros; rewrite Mem_cons_eq; right; auto.
Qed.
simpl.
apply NotBadL_appl_split1 in H4; destruct H4 as (L1, (H4, H6)).
rewrite SL_appl; simpl in *.
apply IHtypes_LF1 with (G:=G)(Gamma:=Gamma); auto.
intros; apply H3; simpl; auto; rewrite in_union; left; auto.
unfold NotBadL in *; intros; simpl in *.
apply H6 with A0 N0.
apply H4 in H7.

(*
(* This assumes that bte 0 actually was present in M
 -- we need to add a case where it was not! *)
skip.
(* appl *)

(******************************************************************)



(* These two lemmas may be a little technical because of the way subsets are
   implemented *)
(* fset_finite? *)
Lemma types_LF_term_vars_in_all_vars:
forall M G Gamma A,
  G |= Gamma |- M ::: A ->
  used_vars_te_LF M \c from_list (flat_map (fun x => map fst_ x) (Gamma::G)).
Admitted.

Lemma types_empty_LF_no_free_vars:
forall M G A,
  emptyEquiv_LF G |= nil |- M ::: A ->
  used_vars_te_LF M = \{}.
Admitted.


Lemma apply lc_t_contains_bte; auto.
apply lc_t_contains_bte; auto.
types_LF_lc_t_LF:
forall G Gamma M A,
  G |= Gamma |- M ::: A -> lc_t_LF M.
intros; induction H; constructor; try apply IHHT;
unfold open_LF in *; auto.
assert (exists x, x \notin L) by apply Fresh; destruct H1;
assert (x \notin L) by auto;
specialize H0 with x; apply H0 in H1;
apply lc_t_n_LF_subst_t in H0; auto; constructor.
Qed.

Fixpoint S (L: list (var * te_LF * ty)) (M: te_LF) : te_LF :=
match L with
| nil => M
| (v, C, A) :: L' => [C // fte v] (S L' M)
end.


Inductive GoodS: list (var * te_LF * ty) -> te_LF -> Prop :=
| nilS: forall M, GoodS nil M
| consS:
    forall L M v C A,
      GoodS L M ->
      v \in used_vars_te_LF (S L M) ->
      lc_t_LF C ->
      Red C A ->
      GoodS ((v, C, A)::L) M
.

Definition fullS L M := GoodS L M /\ used_vars_te_LF (S L M) = \{}.

Lemma S_lam:
forall L A M,
  S L (lam_LF A M) = lam_LF A (S L M).
induction L; intros; simpl in *; eauto;
destruct a; destruct p; rewrite IHL; eauto.
Qed.

Lemma S_appl:
forall L M N,
  S L (appl_LF M N) =
  appl_LF (S L M) (S L N).
induction L; intros; simpl in *; eauto;
destruct a; destruct p; rewrite IHL; eauto.
Qed.

Lemma S_box:
forall L M,
  S L (box_LF M) = box_LF (S L M).
induction L; intros; simpl in *; eauto;
destruct a; destruct p; rewrite IHL; eauto.
Qed.

Lemma S_unbox:
forall L M,
  S L (unbox_LF M) = unbox_LF (S L M).
induction L; intros; simpl in *; eauto;
destruct a; destruct p; rewrite IHL; eauto.
Qed.

Lemma S_hyp:
forall L v A,
  fullS L (hyp_LF (fte v)) ->
  Red (S L (hyp_LF (fte v))) A.
unfold fullS; intros; destruct H.
generalize dependent A;
generalize dependent v;
induction L; intros; simpl in *.
assert (v \in \{v}) by (rewrite in_singleton; auto);
rewrite H0 in H1; apply notin_empty in H1; contradiction.
destruct a; destruct p; simpl in *.
inversion H; subst.
Admitted. (* !!! *)

Lemma GoodS_lc_t:
forall L M,
  GoodS L M ->
  forall C,
    Mem C (map snd_ (map fst_ L)) -> lc_t_LF C.
induction L; intros; simpl in *; rew_map in *.
rewrite Mem_nil_eq in H0; contradiction.
destruct a; destruct p; simpl in *; rewrite Mem_cons_eq in H0;
inversion H; subst; destruct H0; subst; eauto.
Qed.

Lemma subst_t_bound_subst_free_vars:
forall L M v k,
  GoodS L M ->
  ~ Mem v (map fst_ (map fst_ L)) ->
  [hyp_LF (fte v) // bte k](S L M) =
  S L ([hyp_LF (fte v) // bte k] M).
induction L; intros; simpl in *; auto.
destruct a; destruct p; rew_map in *;
assert ( v0 <> v) by (intro; elim H0; rewrite Mem_cons_eq; left; auto);
simpl in *; rewrite <- subst_t_comm_LF; auto.
inversion H; subst; rewrite IHL; auto.
intro; elim H0; rewrite Mem_cons_eq; right; auto.
apply GoodS_lc_t with (C:=t0) in H; auto; rew_map; simpl; apply Mem_here.
Qed.

Lemma S_lc_t_LF:
forall L M,
  GoodS L M ->
  lc_t_LF M ->
  lc_t_LF (S L M).
induction L; intros; simpl in *; eauto;
destruct a; destruct p.
apply lc_t_subst_t_LF_free; [ | eapply IHL; eauto];
inversion H; subst; auto.
Qed.

Lemma GoodS_lam:
forall L0 L M A,
  GoodS L (lam_LF A M) ->
  forall v, v \notin L0 ->
    GoodS L ([hyp_LF (fte v)//bte 0]M).
induction L; intros; simpl in *; try constructor;
destruct a; destruct p; constructor; inversion H; subst; auto.
eapply IHL; eauto.
skip. (* !!! *)
Qed.

Lemma main_attempt1:
forall G Gamma M A L,
  G |= Gamma |- M ::: A ->
  fullS L M ->
  Red (S L M) A.
unfold fullS in *;
intros; assert (lc_t_LF M) by (eapply types_LF_lc_t_LF in H; eauto);
generalize dependent L. induction H; intros; subst.
(* hyp *)
apply S_hyp; unfold fullS; auto.
(* lam *)
destruct H2; rewrite S_lam; apply reducible_abstraction; auto; intros.
rewrite <- S_lam; apply S_lc_t_LF; auto.
unfold open_LF in *;
assert (exists v, v \notin L \u used_vars_te_LF (S L0 M) \u
       from_list (map fst_ (map fst_ L0))) as HF
  by apply Fresh; destruct HF;
rewrite subst_t_neutral_free_LF with (v:=x); eauto;
rewrite subst_t_bound_subst_free_vars.
assert (x \in used_vars_te_LF (S L0 [hyp_LF (fte x) // bte 0]M) \/
        x \notin used_vars_te_LF (S L0 [hyp_LF (fte x) // bte 0]M)).
  skip. (* !!! *)
destruct H7.
(* in *)
replace ([M0 // fte x](S L0 [hyp_LF (fte x) // bte 0]M))
  with (S ((x, M0, A) :: L0) [hyp_LF (fte x) // bte 0] M) by (simpl; auto).
apply H0; eauto.
inversion H1; subst; apply lc_t_subst_t_LF_bound; auto; constructor.
simpl. split.
constructor; auto; apply GoodS_lam with (L0:=L)(A:=A); eauto.
rewrite <- subst_t_bound_subst_free_vars.
rewrite <- subst_t_neutral_free_LF.
Admitted.

Lemma main_conclusion1:
forall G M A,
  emptyEquiv_LF G |= nil |- M ::: A ->
  SN M.
intros; apply property_1 with (A:=A).
apply types_LF_lc_t_LF in H; auto.
apply main_attempt1 with (L:=nil) in H; auto.
split; simpl in *; [constructor | apply types_empty_LF_no_free_vars in H; auto].
Qed.


(* Idea: gather all free variables from a term,
         substitute them with reducible terms of appropriate type
         conclude that the resulting term is reducible *)

Fixpoint subst_free_vars (D: list (var*ty))
         (L: list te_LF) N :=
match D, L with
| nil, _ => N
| _, nil => N
| (v, _ )::V', l::L' => [l // fte v] (subst_free_vars V' L' N)
end.

Fixpoint subst_typing G (L: list te_LF) (D: list (var * ty)) :=
match L, D with
| nil, nil => True
| M ::L', (v, A) :: D' =>
  emptyEquiv_LF G |= nil |- M ::: A /\ (subst_typing G L' D')
| _, _ => False
end.

Fixpoint red_list (L: list te_LF) (D: list (var * ty)) :=
match L, D with
| nil, nil => True
| M :: L', (v, A):: D' => Red M A /\ red_list L' D'
| _, _ => False
end.

Lemma subst_free_vars_notin:
forall D L,
  red_list L D ->
  ok_LF D nil ->
  forall v,
    ~ Mem v (map fst_ D) ->
    subst_free_vars D L (hyp_LF (fte v)) = hyp_LF (fte v).
induction D; intros; simpl in *; auto; destruct a; rew_map in *; simpl in *;
rewrite Mem_cons_eq in *; destruct L; auto.
simpl in *; destruct H; inversion H0; subst.
rewrite IHD; simpl; eauto.
case_if; auto; inversion H3; subst. elim H1; left; auto.
inversion H0; subst; eapply ok_LF_used_weakening in H8; auto.
Qed.

Lemma ok_LF_step:
forall D v (A:ty) U,
  ok_LF ((v, A) :: D) U -> ~ Mem v (map fst_ D).
induction D; intros; rew_map.
rewrite Mem_nil_eq; auto.
destruct a; intro nn; rewrite Mem_cons_eq in nn; simpl in *; destruct nn; subst.
inversion H; inversion H5; subst; elim H10; apply Mem_here.
specialize IHD with v A (v0::U).
apply ok_LF_permut with (G':= (v0,t) :: (v, A) :: D) in H; [|permut_simpl].
inversion H; subst; apply IHD in H6; contradiction.
Qed.

Lemma used_vars_te_LF_subst_t:
forall N C k,
  used_vars_te_LF ([C // bte k] N) = used_vars_te_LF N \/
  used_vars_te_LF ([C // bte k] N) = used_vars_te_LF C \u used_vars_te_LF N.
induction N; intros; simpl in *.
destruct v; case_if; simpl;
[right; rewrite union_empty_r | left | left ]; auto.
destruct IHN with C (S k); rewrite <- H; [left | right]; auto.
destruct IHN1 with C k; destruct IHN2 with C k; rewrite H; rewrite H0;
[left | right | right | right]; auto.
rewrite <- union_comm_assoc; auto.
rewrite union_assoc; auto.
rewrite <- union_comm_assoc.
rewrite <- union_assoc.
assert (forall N,
          used_vars_te_LF C \u used_vars_te_LF C \u N = used_vars_te_LF C \u N).
intros; rewrite union_assoc; rewrite union_same; auto.
rewrite H1; auto.
destruct IHN with C k; rewrite H; [left | right]; auto.
destruct IHN with C k; rewrite H; [left | right]; auto.
Qed.

Lemma Mem_map_fst:
forall A B D (x:A) (t:B),
  Mem (x, t) D -> Mem x (map fst_ D).
induction D; intros.
rewrite Mem_nil_eq in H; contradiction.
destruct a; rewrite Mem_cons_eq in H; destruct H; rew_map; simpl.
inversion H; subst; apply Mem_here.
rewrite Mem_cons_eq; right; eauto.
Qed.


Lemma free_vars_empty_subst_typing:
forall G L D,
  subst_typing G L D ->
  forall t, Mem t L -> used_vars_te_LF t = \{}.
induction L; destruct D; intros; simpl in *.
rewrite Mem_nil_eq in H0; contradiction.
contradiction.
contradiction.
rewrite Mem_cons_eq in H0; destruct H0; subst; destruct p; destruct H.
eapply types_empty_LF_no_free_vars; eauto.
eauto.
Qed.

Lemma subst_free_vars_single_occ:
forall D L A G t v0 v,
  subst_typing G (t::L) ((v0,A)::D) ->
  ok_LF ((v0, A) :: D) nil ->
  (v = v0 -> [t // fte v0](subst_free_vars D L (hyp_LF (fte v))) = t) /\
  (v <> v0 ->  [t // fte v0](subst_free_vars D L (hyp_LF (fte v))) =
    subst_free_vars D L (hyp_LF (fte v))).
intros.
remember (t::L) as L'.
remember ((v0,A)::D) as D'.
generalize dependent A;
generalize dependent t;
generalize dependent v0;
generalize dependent v;
generalize dependent D;
generalize dependent L.
(*
induction H.
generalize dependent G;
generalize dependent D';
generalize dependent L'.
induction L'; destruct D'; intros; simpl in *;
inversion HeqL'; inversion HeqD'; subst; split; intros;
destruct H.
inversion H0; subst; clear HeqL' HeqD' H7 H0.
destruct IHD' with (t0::L) L D v0 v0 t0 G A; auto.
skip.
assert (v0 <> v1) by (intro; subst; elim H9; apply Mem_here).
destruct IHD with L t1 G t v1 v0; auto. skip.
destruct H1;
destruct IHD with L A G t0 v0 v0; auto. skip.
apply H5 in H3; rewrite H3; apply H11 in H2; rewrite H2; auto.
destruct H; inversion H0; subst; inversion H8; subst;
assert (v0 <> v1) by (intro; subst; elim H9; apply Mem_here).
destruct H2.
destruct IHD with L t1 G t v1 v; auto. skip.
destruct (eq_var_dec v v1).
apply H5 in e; rewrite e; apply closed_subst_t_free_LF.
erewrite free_vars_empty_subst_typing; eauto.
destruct IHD with A L t0 v0 v0. skip.
apply H3 in H0; rewrite H0.
apply H4 in H1; rewrite H1; auto.
*)
Admitted.

Lemma subst_free_vars_hyp:
forall G L D,
  ok_LF D nil ->
  subst_typing G L D ->
  forall v A,
    Mem (v, A) D ->
    exists N,
      Mem N L /\
      subst_free_vars D L (hyp_LF (fte v)) = N.
Admitted.

Lemma red_list_Red:
forall L D N,
  red_list L D ->
  Mem N L ->
  exists A, Red N A.
induction L; destruct D; intros; simpl in *.
rewrite Mem_nil_eq in H0; contradiction.
contradiction.
contradiction.
destruct p; destruct H.
rewrite Mem_cons_eq in H0; destruct H0; eauto;
inversion H0; subst; exists t; auto.
Qed.

Lemma subst_free_vars_hyp_Red:
forall G D L,
  red_list L D ->
  ok_LF D nil ->
  subst_typing G L D ->
  forall v A,
    Mem (v, A) D ->
    Red (subst_free_vars D L (hyp_LF (fte v))) A.
intros.
assert (exists N, Mem N L /\
        subst_free_vars D L (hyp_LF (fte v)) = N).
eapply subst_free_vars_hyp; eauto.
destruct H3 as (N, (H3, H4)).
rewrite H4.
Admitted.

(* !!! *)
Lemma lc_t_subst_free_vars:
forall L D k M,
  (forall N, Mem N L -> lc_t_LF N) ->
  lc_t_n_LF k M ->
  lc_t_n_LF k (subst_free_vars D L M).
Admitted.

(* !!! *)
Lemma subst_t_bound_subst_free_vars:
forall L D M v k,
  ~ Mem v (map fst_ D) ->
  [hyp_LF (fte v) // bte k](subst_free_vars D L M) =
  subst_free_vars D L ([hyp_LF (fte v) // bte k] M).
Admitted.

Lemma types_LF_lc_t_LF:
forall G Gamma M A,
  G |= Gamma |- M ::: A -> lc_t_LF M.
intros; induction H; simpl in *; constructor; eauto.
Admitted.

Lemma subst_free_vars_type:
forall G Gamma M A L G',
  G |= Gamma |- M ::: A ->
  concat (Gamma::G) *=* G' ->
  subst_typing G L G' ->
  G |= Gamma |- subst_free_vars G' L M ::: A.
Admitted.

Lemma map_permut_fst:
forall (G: list (var * ty)) G',
  G *=* G' -> map fst_ G *=* map fst_ G'.
Admitted.

Lemma subst_free_vars_lam:
forall D L A M,
  subst_free_vars D L (lam_LF A M) = lam_LF A (subst_free_vars D L M).
induction D; intros; simpl in *; eauto;
destruct a; destruct L; auto. rewrite IHD; simpl; auto.
Qed.

Lemma subst_free_vars_appl:
forall D L M N,
  subst_free_vars D L (appl_LF M N) =
  appl_LF (subst_free_vars D L M) (subst_free_vars D L N).
induction D; intros; simpl in *; eauto;
destruct a; destruct L; auto; rewrite IHD; simpl; auto.
Qed.

Lemma subst_free_vars_box:
forall D L M,
  subst_free_vars D L (box_LF M) = box_LF (subst_free_vars D L M).
induction D; intros; simpl in *; eauto;
destruct a; destruct L; auto; rewrite IHD; simpl; auto.
Qed.

Lemma subst_free_vars_unbox:
forall D L M,
  subst_free_vars D L (unbox_LF M) = unbox_LF (subst_free_vars D L M).
induction D; intros; simpl in *; eauto;
destruct a; destruct L; auto; rewrite IHD; simpl; auto.
Qed.

Lemma subst_typing_lc:
forall L G G0 M,
  subst_typing G0 L G ->
  Mem M L ->
  lc_t_LF M.
induction L; destruct G; simpl; intros.
rewrite Mem_nil_eq in H0; contradiction.
contradiction.
contradiction.
destruct p; rewrite Mem_cons_eq in *; destruct H0; destruct H.
inversion H0; subst.
apply types_LF_lc_t_LF in H; auto.
eapply IHL with (G:=G); eauto.
Qed.

Theorem subst_types_reducible:
forall M G Gamma A L G'
  (H_lc: lc_t_LF M)
  (HT: emptyEquiv_LF G |= nil |- M ::: A)
  (HPermut: concat (Gamma :: G) *=* G')
  (HRed: red_list L G')
  (HRedType: subst_typing G L G'),
  Red (subst_free_vars G' L M) A.
intros; generalize dependent L; generalize dependent G';
induction HT; intros; inversion H_lc; subst; rew_app in *; rew_concat in *;
simpl in *.
(* hyp *)
apply subst_free_vars_hyp_Red with (G:=G); auto.
apply ok_LF_permut with (G:=concat (Gamma::G)); unfold ok_Bg_LF in Ok; auto.
apply Mem_permut with (l:=Gamma ++ concat G); auto;
rewrite Mem_app_or_eq; left; auto.
(* lam *)
intros; rewrite subst_free_vars_lam; apply property_3.
repeat constructor; auto; apply lc_t_subst_free_vars; auto.
intros; eapply subst_typing_lc; eauto.
constructor.
intros; inversion H1; subst; [ | inversion H8].
assert (exists x, x\notin L \u from_list (map fst_ G')
       \u used_vars_te_LF (subst_free_vars G' L0 M))
  by apply Fresh. destruct H2.
unfold open_LF in *; rewrite subst_t_neutral_free_LF with (v:=x).
rewrite subst_t_bound_subst_free_vars.
specialize H0 with x L0 G';
assert (x \notin L) as HH by eauto.
apply H0 with ((x, A)::G') (N::L0) in HH; simpl in *;
auto.
apply lc_t_subst_t_LF_bound; auto; constructor.
rew_app; rew_concat; rewrite HPermut; auto.
apply notin_Mem; rew_concat in H2; eauto.
eauto.
(* appl *)
rewrite subst_free_vars_appl; eapply IHHT1 with (G:=G)(Gamma:=Gamma); eauto.
apply lc_t_subst_free_vars; auto; intros; eapply subst_typing_lc; eauto.
eapply subst_free_vars_type; auto.
(* box *)
apply property_3.
constructor; apply lc_t_subst_free_vars; auto;
intros; eapply subst_typing_lc; eauto.
constructor.
intros. inversion H; subst.
rewrite subst_free_vars_box in H0; inversion H0; subst.
eapply IHHT; eauto.
rew_app; rewrite <- HPermut; auto.
rewrite subst_free_vars_box in H3; inversion H3.
(* unbox *)
rewrite subst_free_vars_unbox; eapply IHHT; eauto.
rewrite subst_free_vars_unbox; apply IHHT; auto.
rewrite <- HPermut; rew_concat; permut_simpl;
apply PPermut_concat_permut in H; rewrite <- H; rew_concat; permut_simpl.
Qed.
*)