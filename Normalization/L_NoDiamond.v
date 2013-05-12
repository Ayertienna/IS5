Add LoadPath "..".
Add LoadPath "../Labeled/Lists/NoDiamond".
Require Import LND_Shared.
Require Import LabeledNoDia.
Require Import ListLib.
Require Import LibTactics.

Open Scope is5_scope.
Open Scope labeled_is5_scope.
Open Scope permut_scope.

Lemma closed_t_succ_L:
forall M n,
  lc_t_n_L n M -> lc_t_n_L (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_L.
Qed.

Lemma lc_t_subst_t_L_bound:
forall M N n,
  lc_t_n_L n N ->
  lc_t_n_L (S n) M ->
  lc_t_n_L n ([N//bte n] M).
induction M; intros; simpl in *; inversion H0; subst; repeat case_if;
try constructor; eauto.
assert (n <> v0) by (intro; subst; elim H1; auto); omega.
eapply IHM; auto; apply closed_t_succ_L; auto.
Qed.

Lemma lc_t_subst_t_L_free:
forall M N n v,
  lc_t_n_L n N ->
  lc_t_n_L n M ->
  lc_t_n_L n ([N//fte v] M).
induction M; intros; simpl in *; inversion H0; subst; repeat case_if;
try constructor; eauto.
eapply IHM; eauto; apply closed_t_succ_L; auto.
Qed.

Lemma lc_w_n_L_subst_t2:
forall N M v n,
lc_w_n_L n (subst_t_L M v N) ->
lc_w_n_L n N.
induction N; intros; simpl in *; try destruct v; constructor;
inversion H; subst; try eapply IHN; eauto.
Qed.

Lemma lc_w_n_L_subst_w2:
forall N w n,
lc_w_n_L n (subst_w_L N (fwo w) (bwo n)) ->
lc_w_n_L (S n) N.
induction N; intros; simpl in *; try destruct v; constructor;
inversion H; subst; try eapply IHN; eauto;
repeat case_if; inversion H0; subst; try inversion H1; subst;
try omega.
Qed.

Lemma lc_t_n_L_subst_w2:
forall N w w' n,
lc_t_n_L n (subst_w_L N w w') ->
lc_t_n_L n N.
induction N; intros; simpl in *; try destruct v; constructor;
inversion H; subst; try eapply IHN; eauto.
Qed.

Lemma lc_t_n_L_subst_t2:
forall N M n,
lc_t_n_L n M ->
lc_t_n_L n (subst_t_L M (bte n) N) ->
lc_t_n_L (S n) N.
induction N; intros; simpl in *; try destruct v; constructor;
repeat case_if; try inversion H1; subst; try omega;
inversion H0; subst; eauto.
apply IHN with (M:=M); eauto; apply closed_t_succ_L; auto.
Qed.

Lemma lc_t_step_L:
forall M N w,
  lc_t_L M ->
  (M, w) |-> (N, w) ->
  lc_t_L N.
Admitted.

Lemma lc_w_step_L:
forall M M' w,
  lc_w_L M ->
  step_L (M, w) (M', w) ->
  lc_w_L M'.
Admitted.

Lemma closed_subst_t_L_free:
forall M v0 N
  (H_lc: v0 \notin used_vars_term_L N),
  [M // fte v0] N = N.
induction N; intros; simpl in *;
repeat case_if;
try (rewrite IHN || (rewrite IHN1; try rewrite IHN2); auto);
[ rewrite notin_singleton in H_lc; elim H_lc |
  destruct v]; auto.
Qed.

Lemma subst_w_L_neutral_bound:
forall M n
  (HT: lc_w_n_L n M),
  forall m w w',
    m >= n -> {{w//bwo m}}({{bwo m// w'}}M) = {{w//w'}}M.
intros M n HT; induction HT; intros; simpl in *; auto.
rewrite IHHT; auto.
rewrite IHHT1; try rewrite IHHT2; auto.
destruct w; destruct w'; simpl; try rewrite IHHT; auto; omega.
repeat case_if; rewrite IHHT; auto.
repeat case_if; rewrite IHHT; auto; inversion H1; subst; omega.
repeat case_if; rewrite IHHT; auto.
inversion H1; subst; omega.
Qed.

Lemma types_L_lc_w_L:
forall Omega Gamma M A w,
  Omega; Gamma |- M ::: A @ w -> lc_w_L M.
intros; induction H; constructor; try apply IHHT;
unfold open_w_L in *; unfold open_t_L in *;
auto.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0. apply lc_w_n_L_subst_t2 in H0; auto.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0; apply lc_w_n_L_subst_w2 in H0; auto.
Qed.

Lemma types_L_lc_t_L:
forall Omega Gamma M A w,
  Omega; Gamma |- M ::: A @ w -> lc_t_L M.
intros; induction H; constructor; try apply IHHT;
unfold open_w_L in *; unfold open_t_L in *;
auto.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0;
apply lc_t_n_L_subst_t2 in H0; auto; constructor.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0;
apply lc_t_n_L_subst_w2 in H0; auto; constructor.
Qed.

Definition normal_form (M: te_L) := value_L M.

Inductive neutral_L: te_L -> Prop :=
| nHyp: forall n, neutral_L (hyp_L n)
| nAppl: forall M N, neutral_L (appl_L M N)
| nUnbox: forall M, neutral_L (unbox_L M)
| nFetch: forall M w, neutral_L (fetch_L w M)
.

Lemma value_no_step:
forall M,
  value_L M ->
  forall N w , ~ (M, w) |-> (N, w).
induction M; intros; intro;
try inversion H0; inversion H1; subst;
inversion H; subst; eapply IHM; eauto; try omega.
Qed.

Lemma neutral_or_value:
forall M,
  neutral_L M \/ value_L M.
induction M; intros;
try (destruct IHM; [left | right]; constructor; auto).
left; constructor.
right; constructor.
left; constructor.
right; constructor.
left; constructor.
left; constructor.
Qed.

Lemma neutral_not_value:
forall M,
  neutral_L M -> ~ value_L M.
induction M; intros; intro; inversion H; inversion H0.
Qed.

Inductive WT: var -> te_L -> Prop :=
| val_WT: forall V w, value_L V -> WT w V
| step_WT: forall M w, (exists V, value_L V /\ steps_L M V (fwo w)) -> WT w M
.

Lemma step_L_unique:
forall M N N' w,
(M, w) |-> (N, w) -> (M, w) |-> (N', w) -> N = N'.
intros; generalize dependent N'.
remember (M,w) as M''; remember (N, w) as N'.
generalize dependent M;
generalize dependent N;
generalize dependent w.
induction H; intros; inversion HeqN'; inversion HeqM''; subst; auto.
inversion H3; subst; auto; inversion HRed.
inversion H1; subst; auto; inversion HRed.
inversion H4; subst; auto. inversion H. erewrite IHstep_L with (N:=M'); eauto.
inversion H2; subst; auto. inversion H. erewrite IHstep_L with (N:=M'); eauto.
Focus 2. inversion H1; subst.
apply value_no_step in HRed; auto; contradiction. auto.
inversion H2; subst.
assert (M'=M'0).
erewrite IHstep_L with (w0:=w) (N:=M'); eauto.
subst; auto.
apply value_no_step in H; auto; contradiction.
Qed.

Lemma WT_step:
forall M M' w,
  WT w M ->
  (M, fwo w) |-> (M', fwo w) ->
  WT w M'.
intros; inversion H; subst.
apply value_no_step in H0; auto; contradiction.
destruct H1 as (V, (H1, H2)).
inversion H2; subst.
apply step_L_unique with (N':=V) in H0; subst; auto. constructor; auto.
apply step_WT; exists V; split; auto.
apply step_L_unique with (N':=M'0) in H0; subst; auto.
Qed.

Lemma WT_step_back:
forall M M' w,
  (M, fwo w) |-> (M', fwo w) ->
  WT w M' -> WT w M.
intros; apply step_WT.
inversion H0; subst.
exists M'; split; auto; constructor; auto.
destruct H1; destruct H1.
exists x; split; auto; apply stepm_L with (M':=M'); auto.
Qed.

Hint Resolve WT_step WT_step_back.

Fixpoint Red (M: te_L) (A: ty) (w:var): Prop :=
match A with
| tvar => WT w M
| tarrow A1 A2 =>
    (WT w M /\
    forall N
           (H_lc_t: lc_t_L N)
           (H_lc_w: lc_w_L N)
           (HRed: Red N A1 w),
      Red (appl_L M N) A2 w)
| tbox A1 => WT w M /\ Red (unbox_L M) A1 w
end.

(* CR 2 *)
Theorem property_2:
forall A M M' w
  (HRed: Red M A w)
  (H_lc_t: lc_t_L M)
  (H_lc_w: lc_w_L M)
  (HStep: (M, fwo w) |-> (M', fwo w)),
  Red M' A w.
induction A; intros; simpl in *; intros.
(* base type *)
eauto.
(* arrow type *)
destruct HRed; split; eauto; intros.
apply IHA2 with (M:=appl_L M N); auto; constructor; auto.
(* box type *)
destruct HRed; split; eauto; intros.
apply IHA with (M:=unbox_L M); auto;
repeat constructor; auto.
Qed.

(* CR 1 *)
Theorem property_1:
forall A M w
  (H_lc_t: lc_t_L M),
  Red M A w -> WT w M.
induction A; intros; simpl in *; auto;
destruct H; auto.
Qed.

(* CR 3 *)
Theorem property_3:
forall A M M' w
  (H_lct: lc_t_L M)
  (H_lcw: lc_w_L M),
  (M, fwo w) |-> (M', fwo w) ->
  Red M' A w ->
  Red M A w.
induction A; intros; simpl in *.
(* base type *)
eauto.
(* arrow type *)
destruct H0; split; eauto; intros.
apply IHA2 with (appl_L M' N); try constructor; auto; intros; simpl in *.
(* box type *)
destruct H0; split; eauto; intros.
intros; apply IHA with (unbox_L M'); try constructor; auto.
Qed.

Fixpoint find_var (L: list (var * var * ty * te_L)) (x:var) :
                     option (var * var * ty * te_L) :=
match L with
| nil => None
| (w, v, A, M) :: L' =>
  if (eq_var_dec x v) then Some (w, v, A, M) else find_var L' x
end.

Fixpoint find_world (L: list (var * var)) (w:vwo) : option (var * var) :=
match L with
| nil => None
| (w0, w1) :: L' =>
  if (eq_vwo_dec w (fwo w1)) then Some (w0, w1) else find_world L' w
end.

Fixpoint SL (L: list (var * var * ty * te_L)) (W: list (var * var)) M :=
match M with
| hyp_L (bte v) => M
| hyp_L (fte v) =>
  let x := find_var L v in
  match x with
    | Some (v, A, M) => M
    | None => hyp_L (fte v)
  end
| lam_L A M => lam_L A (SL L W M)
| appl_L M N => appl_L (SL L W M) (SL L W N)
| box_L M => box_L (SL L W M)
| unbox_L M => unbox_L (SL L W M)
| fetch_L w M =>
  let x := find_world W w in
  match x with
      | Some (x0, x1) => fetch_L (fwo x0) (SL L W M)
      | None => fetch_L w (SL L W M)
  end
end.

Fixpoint OkL (L: list (var * var * ty * te_L)) U :=
match L with
| nil => True
| (w, v, A, M) :: L' => ~ Mem v U /\ OkL L' (v::U)
end.

Lemma OkL_permut:
forall L U1 U2,
  U1 *=* U2 ->
  OkL L U1 -> OkL L U2.
induction L; intros; [constructor | destruct a; destruct p; destruct p];
inversion H0; subst; constructor.
intro; elim H1; apply Mem_permut with (l:=U2); [symmetry | ]; auto.
apply IHL with (U1:=v0::U1); auto.
Qed.

Lemma OkL_weaken:
forall L U w,
  OkL L (w::U) -> OkL L U.
induction L; intros; simpl in *; auto; destruct a; destruct p; destruct p;
destruct H;
split.
intro; elim H; rewrite Mem_cons_eq; right; auto.
apply IHL with w. apply OkL_permut with (U1:=v0::w::U); auto; permut_simpl.
Qed.

Lemma OkL_used_notin:
forall L U x A w M,
  OkL L U ->
  Mem x U ->
  ~ Mem (w, x, A, M) L.
induction L; intros.
rewrite Mem_nil_eq; tauto.
intro; destruct a; destruct p; destruct p; rewrite Mem_cons_eq in *;
inversion H; subst; destruct H1.
inversion H1; subst; contradiction.
specialize IHL with U x A w M.
apply OkL_weaken in H3; apply IHL in H3; auto.
Qed.

Lemma Mem_Red_Hyp:
forall L v A M W w,
  (forall (a : var) (b : var) (c: ty) (d : te_L),
     Mem (a, b, c, d) L → Red d c a) ->
  Mem (w, v, A, M) L ->
  OkL L nil ->
  SL L W (hyp_L (fte v)) = M.
induction L; intros; rew_map in *.
rewrite Mem_nil_eq in H0; contradiction.
destruct a; destruct p; destruct p; simpl in *; case_if.
rewrite Mem_cons_eq in H0; destruct H0.
inversion H0; subst; auto.
destruct H1.
apply OkL_used_notin with (U:=v1::nil) in H0;
  [contradiction | auto | apply Mem_here ].
destruct H1.
apply IHL with A w; auto.
intros; apply H with b; rewrite Mem_cons_eq; right; auto.
rewrite Mem_cons_eq in H0; destruct H0; auto; inversion H0; subst;
elim H2; auto.
apply OkL_weaken in H3; auto.
Qed.

Lemma Mem_fst_:
forall A B (a:A) (b:B) L,
Mem (a, b) L -> Mem a (map fst_ L).
induction L; intros; [rewrite Mem_nil_eq in *; contradiction| ];
rew_map in *; simpl in *; rewrite Mem_cons_eq in *; destruct H; subst;
[left | right]; auto.
Qed.

Lemma Mem_snd_:
forall A B (a:A) (b:B) L,
Mem (a, b) L -> Mem b (map snd_ L).
induction L; intros; [rewrite Mem_nil_eq in *; contradiction| ];
rew_map in *; simpl in *; rewrite Mem_cons_eq in *; destruct H; subst;
[left | right]; auto.
Qed.

Lemma SL_hyp:
  forall L Omega (Gamma: ctx_L) w v A W,
  OkL L nil ->
  Gamma *=* map fst_ L ->
  (forall a b c d, Mem (a, b, c, d) L -> Red d c a) ->
  Omega; Gamma |- hyp_L (fte v) ::: A @ w ->
  Red (SL L W (hyp_L (fte v))) A w.
intros.
assert (Mem (w, v, A) (map fst_ L)).
  apply Mem_permut with (l:= Gamma); auto.
  inversion H2; auto.
assert (exists M, Mem (w, v, A, M) L).
  clear Omega Gamma H0 H2.
  induction L; intros; rew_map in *.
  rewrite Mem_nil_eq in H3; contradiction.
  destruct a; destruct p; destruct p; rewrite Mem_cons_eq in *; destruct H3.
  exists t; simpl in *; inversion H0; subst; auto; apply Mem_here.
  destruct IHL; auto. inversion H; subst; apply OkL_weaken in H3; auto.
  intros; apply H1 with b; rewrite Mem_cons_eq; right; auto.
  exists x; rewrite Mem_cons_eq; right; auto.
destruct H4.
assert (Mem (w, v, A ,x) L) by auto;
apply Mem_Red_Hyp with (W:=W) in H4; auto;
rewrite H4; apply H1 with v; auto.
Qed.

Lemma SL_nil:
forall M,
  SL nil nil M = M.
induction M; intros; simpl in *;
try erewrite IHM || (erewrite IHM1; try erewrite IHM2); eauto.
destruct v; auto.
Qed.

Lemma Mem_find_var:
  forall L v,
    Mem v (map snd_ (map fst_ (map fst_ L))) ->
    exists w A M, find_var L v = Some (w, v, A, M).
induction L; intros; [ rewrite Mem_nil_eq in *; contradiction | ];
destruct a; destruct p; destruct p; rew_map in *; simpl in *.
subst; rewrite Mem_cons_eq in H.
destruct (eq_var_dec v v1).
subst; simpl; exists v0 t0 t; auto.
destruct H; try contradiction; apply IHL; auto.
Qed.

Lemma NotMem_find_var:
  forall L v,
    ~Mem v (map snd_ (map fst_ (map fst_ L))) ->
    find_var L v = None.
induction L; intros; simpl in *; auto;
destruct a; destruct p; destruct p; rew_map in *; simpl in *;
case_if.
elim H; apply Mem_here.
apply IHL; intro; elim H;
rewrite Mem_cons_eq; right; auto.
Qed.

Lemma find_var_Mem:
forall L w v A M,
  find_var L v = Some (w, v, A, M) -> Mem (w, v, A, M) L.
induction L; intros; [inversion H; subst | ].
destruct a; destruct p; destruct p; simpl in *; case_if.
inversion H; subst; apply Mem_here.
rewrite Mem_cons_eq; right; apply IHL; auto.
Qed.

Lemma lc_SL:
forall M L W n,
  lc_t_n_L n M ->
  (forall a b c d, Mem (a,b,c,d) L -> lc_t_L d) ->
  lc_t_n_L n (SL L W M).
induction M; intros; simpl in *;
try (inversion H; subst; constructor; eapply IHM; eauto).
destruct v; inversion H; subst.
constructor; auto.
destruct (Mem_dec var (map snd_ (map fst_ (map fst_ L))) v). apply eq_var_dec.
apply Mem_find_var in m; destruct m; destruct H1; destruct H1.
rewrite H1. replace n with (0+n) by omega.
apply closed_t_addition_L; apply H0 with x v x0. apply find_var_Mem; auto.
rewrite NotMem_find_var; auto.
inversion H; subst; constructor; [apply IHM1 | apply IHM2]; auto.
destruct (find_world W v); simpl in *; try destruct p; constructor; auto;
apply IHM; inversion H; eauto.
Qed.

Lemma lc_w_SL:
forall M L W n,
  lc_w_n_L n M ->
  (forall a b c d, Mem (a,b,c,d) L -> lc_w_L d) ->
  lc_w_n_L n (SL L W M).
induction M; intros; simpl in *;
try (inversion H; subst; constructor; eapply IHM; eauto).
destruct v; inversion H; subst.
constructor; auto.
destruct (Mem_dec var (map snd_ (map fst_ (map fst_ L))) v). apply eq_var_dec.
apply Mem_find_var in m; destruct m; destruct H1; destruct H1.
rewrite H1. replace n with (0+n) by omega.
apply closed_w_addition_L; apply H0 with x v x0. apply find_var_Mem; auto.
rewrite NotMem_find_var; auto.
inversion H; subst; constructor; [apply IHM1 | apply IHM2]; auto.
destruct (find_world W v); simpl in *; try destruct p;
inversion H; constructor; auto; apply IHM; auto.
Qed.

Lemma SL_bte_subst:
forall L0 W M x k,
  ~ Mem x (map snd_ (map fst_ (map fst_ L0))) ->
  (forall w v a m, Mem (w, v, a, m) L0 -> lc_t_L m) ->
  [hyp_L (fte x) // bte k](SL L0 W M) =
  SL L0 W [hyp_L (fte x) // bte k]M.
induction M; intros; simpl in *;
try rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto.
case_if; simpl.
case_if. rewrite NotMem_find_var; auto.
destruct v; simpl; repeat case_if; auto.
destruct (Mem_dec var (map snd_ (map fst_ (map fst_ L0))) v);
try apply eq_var_dec; [ | rewrite NotMem_find_var]; auto;
simpl; repeat case_if; auto.
apply Mem_find_var in m; destruct m as (a, (w, (b, m))); rewrite m; simpl.
rewrite closed_subst_t_bound_L with (n:=0); auto; try omega;
apply H0 with a v w; apply find_var_Mem; auto.
destruct (find_world W v); simpl in *; try destruct p; simpl;
try erewrite IHM; eauto.
Qed.

Fixpoint FV_L (L: list (var * var * ty * te_L)) :=
match L with
| nil => \{}
| (w, v, A, M) :: L' => used_vars_term_L M \u FV_L L'
end.

Fixpoint FW_L (L: list (var * var * ty * te_L)) :=
match L with
| nil => \{}
| (w, v, A, M) :: L' => used_worlds_term_L M \u FW_L L'
end.

Lemma notin_FV_notin_elem:
forall x L,
  x \notin FV_L L ->
  forall a b c d, Mem (a,b,c, d) L -> x \notin used_vars_term_L d.
induction L; intros; simpl in *.
rewrite Mem_nil_eq in *; contradiction.
rewrite Mem_cons_eq in H0; destruct H0; [inversion H0; subst | ].
rewrite notin_union in H; destruct H; auto.
destruct a; destruct p; destruct p; rewrite notin_union in H; destruct H;
apply IHL with (a:=a0) (b:=b) (c:=c); auto.
Qed.

Lemma notin_FW_notin_elem:
forall x L,
  x \notin FW_L L ->
  forall a b c d, Mem (a,b,c,d) L -> x \notin used_worlds_term_L d.
induction L; intros; simpl in *.
rewrite Mem_nil_eq in *; contradiction.
rewrite Mem_cons_eq in H0; destruct H0; [inversion H0; subst | ].
rewrite notin_union in H; destruct H; auto.
destruct a; destruct p; destruct p; rewrite notin_union in H; destruct H;
apply IHL with (a:=a0) (b:=b) (c:=c); auto.
Qed.

Lemma Mem_find_world:
  forall W w,
    Mem w (map snd_ W) ->
    exists w', find_world W (fwo w) = Some (w', w).
induction W; intros; [ rewrite Mem_nil_eq in *; contradiction | ];
destruct a; rew_map in *; simpl in *.
subst; rewrite Mem_cons_eq in H.
destruct H; subst.
exists v; case_if; auto.
case_if; [inversion H0; subst | ].
exists v; auto.
apply IHW; auto.
Qed.

Lemma NotMem_find_world:
  forall W w,
    ~Mem w (map snd_ W) ->
    find_world W (fwo w) = None.
induction W; intros; simpl in *; auto;
destruct a; rew_map in *; simpl in *; case_if.
inversion H0; subst; elim H; apply Mem_here.
apply IHW; intro; elim H; rewrite Mem_cons_eq; right; auto.
Qed.

Lemma find_world_Mem:
forall W w w',
  find_world W (fwo w) = Some (w', w) -> Mem (w', w) W.
induction W; intros; [inversion H; subst | ].
destruct a; simpl in *; case_if.
inversion H; subst; apply Mem_here.
rewrite Mem_cons_eq; right; apply IHW; auto.
Qed.

Lemma SL_extend_L:
forall M L0 W w x A N,
  x \notin FV_L L0 ->
  ~Mem x (map snd_ (map fst_ (map fst_ L0))) ->
  SL ((w, x, A, N) :: L0) W M =
  [N // fte x](SL L0 W M).
induction M; intros; simpl in *;
try rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto.
destruct v; simpl; repeat case_if; auto.
rewrite NotMem_find_var; auto; simpl; case_if; auto.
destruct (Mem_dec var (map snd_ (map fst_ (map fst_ L0))) v);
try apply eq_var_dec; [ | rewrite NotMem_find_var]; auto;
simpl; repeat case_if; auto.
apply Mem_find_var in m; destruct m as (w', (a, (b, m))); rewrite m; simpl.
rewrite closed_subst_t_L_free; auto.
apply notin_FV_notin_elem with L0 w' v a; eauto.
apply find_var_Mem; eauto.
destruct (find_world W v); simpl; try destruct p; auto.
Qed.

Lemma find_world_bound_None:
forall W k,
  find_world W (bwo k) = None.
induction W; intros; simpl; auto; destruct a; case_if; auto.
Qed.

Lemma SL_extend_W:
forall M L W w0 w1,
  ~ Mem w1 (map snd_ W) ->
  w1 \notin FW_L L ->
  ~ Mem w1 (map fst_ W) ->
  SL L ((w0, w1)::W) M =
  {{fwo w0 // fwo w1}}(SL L W M).
induction M; intros; simpl in *; repeat (case_if; simpl in *);
try rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto;
try (apply NotMem_find_world in H; rewrite H; simpl; case_if; auto).
destruct v; simpl; repeat case_if; auto;
destruct (Mem_dec var (map snd_ (map fst_ (map fst_ L))) v);
try apply eq_var_dec; [ | rewrite NotMem_find_var]; auto;
simpl; repeat case_if; auto;
apply Mem_find_var in m; destruct m as (w', (a, (b, m))); rewrite m; simpl;
rewrite closed_subst_w_free_L; auto;
apply notin_FW_notin_elem with L w' v a; eauto; apply find_var_Mem; eauto.
destruct v; [rewrite find_world_bound_None | ]; simpl; repeat case_if; auto;
destruct (Mem_dec var (map snd_ W) v); [ apply eq_var_dec | | ];
[ | rewrite NotMem_find_world]; auto; simpl; repeat case_if; auto;
apply Mem_find_world in m; destruct m as (wa, m); rewrite m; simpl;
case_if; auto; inversion H3; subst;
apply find_world_Mem in m; apply Mem_fst_ in m; contradiction.
Qed.

Lemma OkL_fresh:
forall L x U,
  OkL L U ->
  x \notin from_list (map snd_ (map fst_ (map fst_ L))) \u from_list U ->
  OkL L (x::U).
induction L; intros; [constructor | destruct a; destruct p; destruct p];
simpl in *; destruct H; split.
intro; elim H; rewrite Mem_cons_eq in *; destruct H2; subst; auto;
repeat rewrite notin_union in *; destruct H0; destruct H0;
rew_map; simpl; rewrite from_list_cons; rewrite in_union; left;
rewrite in_singleton; auto.
apply OkL_permut with (U1:=x::v0::U); [permut_simpl | apply IHL]; auto.
rew_map in *; simpl in *;
repeat rewrite from_list_cons in *; repeat rewrite notin_union in *;
simpl in *; destruct H0; destruct H0; split; auto.
Qed.

Lemma SL_subst_w:
forall M L W w k,
  (forall a b c d, Mem (a, b, c, d) L -> lc_w_L d) ->
  ~ Mem w (map snd_ W) ->
  {{fwo w // bwo k}}(SL L W M) =
  SL L W {{fwo w//bwo k}}M.
induction M; intros; simpl; auto;
try (erewrite IHM || (erewrite IHM1; try erewrite IHM2));
eauto.
destruct v; simpl; auto;
destruct (Mem_dec var (map snd_ (map fst_ (map fst_ L))) v);
[apply eq_var_dec | |].
apply Mem_find_var in m; destruct m; destruct H1; destruct H1;
rewrite H1; apply find_var_Mem in H1;
rewrite closed_subst_w_bound_L with (n:=0); auto;
try omega; apply H with x v x0; auto.
apply NotMem_find_var in n; rewrite n; simpl; auto.

case_if.
  rewrite find_world_bound_None; rewrite NotMem_find_world; auto; simpl;
  case_if; rewrite IHM; eauto.
  destruct v; [rewrite find_world_bound_None | ]; simpl; repeat case_if; auto.
    rewrite IHM; eauto.
    destruct (Mem_dec var (map snd_ W) v); [apply eq_var_dec | |];
    [ | rewrite NotMem_find_world]; auto; simpl; repeat case_if; auto;
    [ | rewrite IHM; eauto];
    apply Mem_find_world in m; destruct m as (wa, m); rewrite m; simpl;
    case_if; rewrite IHM; auto.
Qed.

Theorem main_theorem:
forall Omega Gamma M A w,
  lc_t_L M ->
  lc_w_L M ->
  Omega; Gamma |- M ::: A @ w ->
  forall L W,
    OkL L nil ->
    Gamma *=* map fst_ L ->
    (forall a b c d, Mem (a,b,c,d) L -> lc_t_L d) ->
    (forall a b c d, Mem (a,b,c,d) L -> lc_w_L d) ->
    (forall a b c d, Mem (a,b,c,d) L -> Red d c a) ->
    Red (SL L W M) A w.
intros Omega Gamma M A w LC_t LC_w HT.
induction HT; intros.
(* hyp *)
inversion LC_t; subst; try omega;
apply SL_hyp with Omega Gamma; auto;
constructor; auto.
(* lam *)
unfold open_t_L in *;
assert (exists x, x \notin L \u used_vars_term_L (SL L0 W M) \u
       from_list (map snd_ (map fst_ (map fst_ L0))) \u FV_L L0) by apply Fresh;
destruct H5.
assert (forall V, Red V A w -> lc_t_L V -> lc_w_L V ->
           Red (SL ((w, x, A, V) :: L0) W [hyp_L (fte x) // bte 0]M) B w).
intros; apply H; eauto.
apply lc_t_subst_t_L_bound; [ constructor | inversion LC_t]; auto.
apply lc_w_n_L_subst_t; [ inversion LC_w | constructor]; auto.
constructor; [rewrite Mem_nil_eq; tauto | apply OkL_fresh]; auto;
rewrite notin_union; rewrite from_list_nil; split; auto.
rew_map in *; simpl; rewrite <-  H1; rew_concat; auto.
intros; rewrite Mem_cons_eq in *; destruct H9.
inversion H9; subst; auto.
apply H2 with a b c; auto.
intros; rewrite Mem_cons_eq in *; destruct H9.
inversion H9; subst; auto.
apply H3 with a b c; auto.
intros; rewrite Mem_cons_eq in *; destruct H9.
inversion H9; subst; auto.
eapply H4; eauto.
simpl in *; intros. split. repeat constructor.
intros; apply property_3 with ((SL L0 W M)^t^ N).
constructor; auto; constructor; apply lc_SL; auto; inversion LC_t; auto.
constructor; auto; constructor. apply lc_w_SL; auto; inversion LC_w; auto.
constructor; auto.
apply lc_w_SL; auto; inversion LC_w; auto.
unfold open_t_L in *. apply lc_t_subst_L. apply lc_SL; inversion LC_t; auto.
auto.
unfold open_t_L in *.
rewrite subst_t_neutral_free_L with (w:=x); auto.
replace ([N // fte x]([hyp_L (fte x) // bte 0](SL L0 W M))) with
  (SL ((w, x, A, N)::L0) W [hyp_L (fte x) // bte 0] M).
apply H6; auto.
rewrite SL_bte_subst; auto; [ | apply notin_Mem; auto].
rewrite SL_extend_L; auto.
apply notin_Mem; auto.
(* appl *)
simpl in *; inversion LC_t; inversion LC_w; subst;
apply IHHT1; auto.
apply lc_SL; auto.
apply lc_w_SL; auto.
(* box *)
simpl; split. repeat constructor.
apply property_3 with (M':=(SL L0 W M)^w^ (fwo w)).
inversion LC_t; subst; repeat constructor; apply lc_SL; auto.
inversion LC_w; subst; repeat constructor; apply lc_w_SL; auto.
constructor.
apply lc_SL; inversion LC_t; auto.
unfold open_w_L. apply lc_w_subst_L. apply lc_w_SL; inversion LC_w; auto.
unfold open_w_L in *.
assert (exists w, w \notin L \u used_worlds_term_L (SL L0 W M) \u FW_L L0
       \u from_list (map fst_ W) \u from_list (map snd_ W) )
  by apply Fresh. destruct H5.
rewrite subst_w_neutral_free_L with (w_f:=x); eauto;
rewrite SL_subst_w; auto.
replace ({{fwo w // fwo x}}(SL L0 W {{fwo x // bwo 0}}M))
        with (SL L0 ((w,x)::W) {{fwo x // bwo 0}}M).
apply H; auto.
inversion LC_t; subst; apply lc_t_n_L_subst_w; auto.
inversion LC_w; subst; apply lc_w_subst_L; auto.
rewrite SL_extend_W; auto; apply notin_Mem; auto.
apply notin_Mem; auto.
inversion HRed.
(* unbox *)
simpl in *; inversion LC_t; inversion LC_w; subst;
destruct (find_world W (fwo w)); try destruct p;
apply IHHT; auto.
(* fetch *)
skip. (* FIXME! *)
Qed.

Lemma lc_t_n_L_subst_t:
forall N M n,
lc_t_n_L n M ->
lc_t_n_L n (subst_t_L M (bte n) N) ->
lc_t_n_L (S n) N.
induction N; intros; simpl in *; try destruct v; constructor;
repeat case_if; try inversion H1; subst; try omega;
inversion H0; subst; eauto.
apply IHN with (M:=M); eauto; apply closed_t_succ_L; auto.
Qed.

Theorem WT_Lang:
forall Omega M A w,
  Omega; nil |- M ::: A @ w ->
  WT M.
intros; apply property_1 with A.
apply types_L_lc_t_L in H; auto.
apply types_L_lc_w_L in H; auto.
apply main_theorem with (L:=nil) (W:=nil) in H.
rewrite SL_nil in H; auto.
apply types_L_lc_t_L in H; auto.
apply types_L_lc_w_L in H; auto.
constructor.
rew_map; auto.
intros; rewrite Mem_nil_eq in *; contradiction.
intros; rewrite Mem_nil_eq in *; contradiction.
intros; rewrite Mem_nil_eq in *; contradiction.
Qed.