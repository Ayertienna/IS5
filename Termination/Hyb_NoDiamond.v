Add LoadPath "..".
Add LoadPath "../Hybrid/NoDiamond".
Require Import HybridNoDia.
Require Import ListLib.

Open Scope is5_scope.
Open Scope hybrid_is5_scope.
Open Scope permut_scope.

(* FIXME: Finish this variant of the formalization *)

Inductive WHT: te_Hyb -> vwo -> Prop :=
| val_WHT: forall M w, value_Hyb M -> WHT M w
| step_WHT: forall M w,
              (exists V, value_Hyb V /\ steps_Hyb (M, w) (V, w)) -> WHT M w.

Fixpoint Red (M: te_Hyb) (A: ty) (w: vwo): Prop :=
match A with
| tvar => WHT M w
| tarrow A1 A2 =>
  WHT M w /\
  (forall N, lc_t_Hyb N -> lc_w_Hyb N -> Red N A1 w ->
            Red (appl_Hyb M N) A2 w)
| tbox A1 => WHT M w /\
             Red (unbox_fetch_Hyb w M) A1 w
end.

Lemma step_LF_unique:
forall M N N' w,
  (M, w) |-> (N, w) -> (M, w) |-> (N', w) -> N = N'.
intros; remember (M, w) as M0; remember (N, w) as N0; remember (N', w) as N'0;
generalize dependent M; generalize dependent N;
generalize dependent N'; generalize dependent w;
generalize dependent N'0; induction H; intros;
inversion HeqM0; inversion HeqN0; inversion HeqN'0; subst.
inversion H3; auto; inversion HT.
inversion H1; auto; inversion HT.
inversion H4; subst; [inversion H | ].
assert (M' = M'0); [ | subst; auto]; eapply IHstep_Hyb; eauto.
inversion H2; subst; [inversion H | ];
assert (M' = M'0); [ | subst; auto]; eapply IHstep_Hyb; eauto.
Qed.

Lemma WHT_step:
forall M M' w,
  WHT M w ->
  (M, w) |-> (M', w) ->
  WHT M' w.
intros; inversion H; subst.
apply value_no_step with (N:=M')(w:=w) in H1; auto; contradiction.
destruct H1 as (V, (H1, H2)).
inversion H2; subst.
apply step_LF_unique with (N':=V) in H0; subst; auto. constructor; auto.
apply step_WHT; exists V; split; auto.
apply step_LF_unique with (N':=M'0) in H0; subst; auto.
Qed.

Lemma WHT_step_back:
forall M M' w,
  (M, w) |-> (M', w) ->
WHT M' w -> WHT M w.
intros; apply step_WHT.
inversion H0; subst.
exists M'; split; auto; constructor; auto.
destruct H1 as (V, (H1, H2)).
exists V; split; auto; apply multi_step_Hyb with (M':=M'); auto.
Qed.

Hint Resolve WHT_step WHT_step_back.

(* CR 2 *)
Theorem property_2:
forall A M M' w
  (HRed: Red M A (fwo w))
  (H_lc_t: lc_t_Hyb M)
  (H_lc_w: lc_w_Hyb M)
  (HStep:  (M, fwo w) |-> (M', fwo w)),
  Red M' A (fwo w).
induction A; intros; simpl in *; intros.
(* base type *)
eauto.
(* arrow type *)
destruct HRed;
split; eauto; intros.
apply IHA2 with (M:=appl_Hyb M N); auto; constructor; auto.
(* box type *)
destruct HRed; split; auto; intros; eauto.
apply IHA with (M:=unbox_fetch_Hyb (fwo w) M); auto; constructor; auto.
Qed.

(* CR 1 *)
Theorem property_1:
forall A M w
  (H_lc_t: lc_t_Hyb M),
  Red M A w -> WHT M w.
induction A; intros; simpl in *; auto;
destruct H; auto.
Qed.

(* CR 3 *)
Theorem property_3:
forall A M M' w
  (H_lct: lc_t_Hyb M)
  (H_lcw: lc_w_Hyb M),
  (M, fwo w) |-> (M', fwo w) ->
  Red M' A (fwo w) ->
  Red M A (fwo w).
induction A; intros; simpl in *.
(* base type *)
eauto.
(* arrow type *)
destruct H0; split; eauto; intros;
intros; apply IHA2 with (appl_Hyb M' N); try constructor; auto;
intros; simpl in *.
(* box type *)
destruct H0; split; eauto;
intros; apply IHA with (unbox_fetch_Hyb (fwo w) M');
try constructor; auto; intros.
Qed.

(* Idea: A separate list for each context from G *)

Fixpoint find_var (L: list (var * var * ty * te_Hyb)) (x:var) :
                     option (var * var * ty * te_Hyb) :=
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

Fixpoint SL (L: list (var * var * ty * te_Hyb))
         (W: list (var * var)) (M: te_Hyb)
  : te_Hyb :=
match M with
| hyp_Hyb (bte v) => M
| hyp_Hyb (fte v) =>
  let x := find_var L v in
  match x with
    | Some (v, A, M) => M
    | None => hyp_Hyb (fte v)
  end
| lam_Hyb A M => lam_Hyb A (SL L W M)
| appl_Hyb M N => appl_Hyb (SL L W M) (SL L W N)
| box_Hyb M => box_Hyb (SL L W M)
| unbox_fetch_Hyb w M =>
  let x := find_world W w in
  match x with
      | Some (x0, x1) => unbox_fetch_Hyb (fwo x0) (SL L W M)
      | None => unbox_fetch_Hyb w (SL L W M)
  end
end.

Fixpoint OkL (L: list (var * var * ty * te_Hyb)) U :=
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
destruct H; split.
intro; elim H; rewrite Mem_cons_eq; right; auto.
apply IHL with w. apply OkL_permut with (U1:=v0::w::U); auto; permut_simpl.
Qed.

Lemma OkL_used_notin:
forall L U w x A M,
  OkL L U ->
  Mem x U ->
  ~ Mem (w, x, A, M) L.
induction L; intros.
rewrite Mem_nil_eq; tauto.
intro; destruct a; destruct p; destruct p;
rewrite Mem_cons_eq in *; inversion H; subst;
destruct H1.
inversion H1; subst; contradiction.
specialize IHL with U w x A M.
apply OkL_weaken in H3; apply IHL in H3; auto.
Qed.

Lemma Mem_Red_Hyp:
forall L v A M W w,
  (forall (w':var)  (a : var) (b : ty) (c : te_Hyb),
     Mem (w', a, b, c) L → Red c b (fwo w')) ->
  Mem (w, v, A, M) L ->
  OkL L nil ->
  SL L W (hyp_Hyb (fte v)) = M.
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
intros; apply H with a; rewrite Mem_cons_eq; right; auto.
rewrite Mem_cons_eq in H0; destruct H0; auto; inversion H0; subst;
elim H2; auto.
apply OkL_weaken in H3; auto.
Qed.

Lemma SL_hyp:
  forall L G Gamma w v A W,
  OkL L nil ->
  (* 2. & 3. ~ map fst_ L,
     forall w v A M in L, (v, A) in get w (w, Gamma) G *)
  concat (Gamma::(map snd_ G)) *=* map fst_ L ->
  (forall w a b c, Mem (w, a, b, c) L -> Red c b (fwo w)) ->
  G |= (w, Gamma) |- hyp_Hyb (fte v) ::: A ->
  Red (SL L W (hyp_Hyb (fte v))) A (fwo w).
intros.
assert (Mem (v, A) (map fst_ L)).
  apply Mem_permut with (l:= concat (Gamma::map snd_ G)); auto;
  rew_concat; rewrite Mem_app_or_eq; left; inversion H2; subst; auto.
assert (exists M, Mem (v, A, M) L).
  clear G Gamma H0 H2.
  induction L; intros; rew_map in *.
  rewrite Mem_nil_eq in H3; contradiction.
  destruct a; destruct p; rewrite Mem_cons_eq in *; destruct H3.
  exists t; simpl in *; inversion H0; subst; auto; apply Mem_here.
  destruct IHL; auto. inversion H; subst; apply OkL_weaken in H3; auto.
  intros; apply H1 with a; rewrite Mem_cons_eq; right; auto.
  exists x; rewrite Mem_cons_eq; right; auto.
destruct H4.
assert (Mem (v, A ,x) L) by auto;
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
    Mem v (map fst_ (map fst_ L)) ->
    exists A M, find_var L v = Some (v, A, M).
induction L; intros; [ rewrite Mem_nil_eq in *; contradiction | ];
destruct a; destruct p; rew_map in *; simpl in *.
subst; rewrite Mem_cons_eq in H.
destruct (eq_var_dec v v0).
subst; simpl; exists t0 t; auto.
destruct H; try contradiction; apply IHL; auto.
Qed.

Lemma NotMem_find_var:
  forall L v,
    ~Mem v (map fst_ (map fst_ L)) ->
    find_var L v = None.
induction L; intros; simpl in *; auto;
destruct a; destruct p; rew_map in *; simpl in *;
case_if.
elim H; apply Mem_here.
apply IHL; intro; elim H;
rewrite Mem_cons_eq; right; auto.
Qed.

Lemma find_var_Mem:
forall L v A M,
  find_var L v = Some (v, A, M) -> Mem (v, A, M) L.
induction L; intros; [inversion H; subst | ].
destruct a; destruct p; simpl in *; case_if.
inversion H; subst; apply Mem_here.
rewrite Mem_cons_eq; right; apply IHL; auto.
Qed.

Lemma lc_SL:
forall M L W n,
  lc_t_n_Hyb n M ->
  (forall a b c, Mem (a,b,c) L -> lc_t_Hyb c) ->
  lc_t_n_Hyb n (SL L W M).
induction M; intros; simpl in *;
try (inversion H; subst; constructor; eapply IHM; eauto).
destruct v; inversion H; subst.
constructor; auto.
destruct (Mem_dec var (map fst_ (map fst_ L)) v). apply eq_var_dec.
apply Mem_find_var in m; destruct m; destruct H1.
rewrite H1. replace n with (0+n) by omega.
apply closed_t_addition; apply H0 with v x. apply find_var_Mem; auto.
rewrite NotMem_find_var; auto.
inversion H; subst; constructor; [apply IHM1 | apply IHM2]; auto.
destruct (find_world W v); simpl in *; try destruct p; constructor; auto;
apply IHM; inversion H; eauto.
Qed.

Lemma lc_w_SL:
forall M L W n,
  lc_w_n_Hyb n M ->
  (forall a b c, Mem (a,b,c) L -> lc_w_Hyb c) ->
  lc_w_n_Hyb n (SL L W M).
induction M; intros; simpl in *;
try (inversion H; subst; constructor; eapply IHM; eauto).
destruct v; inversion H; subst.
constructor; auto.
destruct (Mem_dec var (map fst_ (map fst_ L)) v). apply eq_var_dec.
apply Mem_find_var in m; destruct m; destruct H1.
rewrite H1. replace n with (0+n) by omega.
apply closed_w_addition; apply H0 with v x. apply find_var_Mem; auto.
rewrite NotMem_find_var; auto.
inversion H; subst; constructor; [apply IHM1 | apply IHM2]; auto.
destruct (find_world W v); simpl in *; try destruct p;
inversion H; constructor; auto; apply IHM; auto.
Qed.

Lemma SL_bte_subst:
forall L0 W M x k,
  ~ Mem x (map fst_ (map fst_ L0)) ->
  (forall v a m, Mem (v, a, m) L0 -> lc_t_Hyb m) ->
  [hyp_Hyb (fte x) // bte k](SL L0 W M) =
  SL L0 W [hyp_Hyb (fte x) // bte k]M.
induction M; intros; simpl in *;
try rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto.
case_if; simpl.
case_if. rewrite NotMem_find_var; auto.
destruct v; simpl; repeat case_if; auto.
destruct (Mem_dec var (map fst_ (map fst_ L0)) v);
try apply eq_var_dec; [ | rewrite NotMem_find_var]; auto;
simpl; repeat case_if; auto.
apply Mem_find_var in m; destruct m as (a, (b, m)); rewrite m; simpl.
rewrite closed_subst_t_Hyb_bound with (n:=0); auto; try omega;
apply H0 with v a; apply find_var_Mem; auto.
destruct (find_world W v); simpl in *; try destruct p; simpl;
try erewrite IHM; eauto.
Qed.

Fixpoint FV_L (L: list (var * ty * te_Hyb)) :=
match L with
| nil => \{}
| (v, A, M) :: L' => free_vars_Hyb M \u FV_L L'
end.

Fixpoint FW_L (L: list (var * ty * te_Hyb)) :=
match L with
| nil => \{}
| (v, A, M) :: L' => free_worlds_Hyb M \u FW_L L'
end.

Lemma notin_FV_notin_elem:
forall x L,
  x \notin FV_L L ->
  forall a b c, Mem (a,b,c) L -> x \notin free_vars_Hyb c.
induction L; intros; simpl in *.
rewrite Mem_nil_eq in *; contradiction.
rewrite Mem_cons_eq in H0; destruct H0; [inversion H0; subst | ].
rewrite notin_union in H; destruct H; auto.
destruct a; destruct p; rewrite notin_union in H; destruct H;
apply IHL with (a:=a0) (b:=b); auto.
Qed.

Lemma notin_FW_notin_elem:
forall x L,
  x \notin FW_L L ->
  forall a b c, Mem (a,b,c) L -> x \notin free_worlds_Hyb c.
induction L; intros; simpl in *.
rewrite Mem_nil_eq in *; contradiction.
rewrite Mem_cons_eq in H0; destruct H0; [inversion H0; subst | ].
rewrite notin_union in H; destruct H; auto.
destruct a; destruct p; rewrite notin_union in H; destruct H;
apply IHL with (a:=a0) (b:=b); auto.
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
forall M L0 W x A N,
  x \notin FV_L L0 ->
  ~Mem x (map fst_ (map fst_ L0)) ->
  SL ((x, A, N) :: L0) W M =
  [N // fte x](SL L0 W M).
induction M; intros; simpl in *;
try rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto.
destruct v; simpl; repeat case_if; auto.
rewrite NotMem_find_var; auto; simpl; case_if; auto.
destruct (Mem_dec var (map fst_ (map fst_ L0)) v);
try apply eq_var_dec; [ | rewrite NotMem_find_var]; auto;
simpl; repeat case_if; auto.
apply Mem_find_var in m; destruct m as (a, (b, m)); rewrite m; simpl.
rewrite closed_subst_t_Hyb_free; auto.
apply notin_FV_notin_elem with L0 v a; eauto.
apply find_var_Mem; eauto.
destruct (find_world W v); simpl; try destruct p; auto.
Qed.

Lemma find_world_bound_None:
forall W k,
  find_world W (bwo k) = None.
induction W; intros; simpl; auto; destruct a; case_if; auto.
Qed.

Lemma Mem_fst_:
forall A B (a:A) (b:B) L,
Mem (a, b) L -> Mem a (map fst_ L).
induction L; intros; [rewrite Mem_nil_eq in *; contradiction| ];
rew_map in *; simpl in *; rewrite Mem_cons_eq in *; destruct H; subst;
[left | right]; auto.
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
destruct (Mem_dec var (map fst_ (map fst_ L)) v);
try apply eq_var_dec; [ | rewrite NotMem_find_var]; auto;
simpl; repeat case_if; auto;
apply Mem_find_var in m; destruct m as (a, (b, m)); rewrite m; simpl;
rewrite closed_subst_w_Hyb_free; auto;
apply notin_FW_notin_elem with L v a; eauto; apply find_var_Mem; eauto.
destruct v; [rewrite find_world_bound_None | ]; simpl; repeat case_if; auto;
destruct (Mem_dec var (map snd_ W) v); [ apply eq_var_dec | | ];
[ | rewrite NotMem_find_world]; auto; simpl; repeat case_if; auto;
apply Mem_find_world in m; destruct m as (wa, m); rewrite m; simpl;
case_if; auto; inversion H3; subst;
apply find_world_Mem in m; apply Mem_fst_ in m; contradiction.
Qed.

Lemma OkL_fresh:
forall L x U,
  OkL L U->
  x \notin from_list (map fst_ (map fst_ L)) \u from_list U ->
  OkL L (x::U).
induction L; intros; [constructor | destruct a; destruct p];
simpl in *; destruct H; split.
intro; elim H; rewrite Mem_cons_eq in *; destruct H2; subst; auto;
repeat rewrite notin_union in *; destruct H0; destruct H0;
rew_map; simpl; rewrite from_list_cons; rewrite in_union; left;
rewrite in_singleton; auto.
apply OkL_permut with (U1:=x::v::U); [permut_simpl | apply IHL]; auto.
rew_map in *; simpl in *;
repeat rewrite from_list_cons in *; repeat rewrite notin_union in *;
simpl in *; destruct H0; destruct H0; split; auto.
Qed.

Lemma SL_subst_w:
forall M L W w k,
  (forall a b c, Mem (a, b, c) L -> lc_w_Hyb c) ->
  ~ Mem w (map snd_ W) ->
  {{fwo w // bwo k}}(SL L W M) =
  SL L W {{fwo w//bwo k}}M.
induction M; intros; simpl; auto;
try (erewrite IHM || (erewrite IHM1; try erewrite IHM2));
eauto.
destruct v; simpl; auto;
destruct (Mem_dec var (map fst_ (map fst_ L)) v);
[apply eq_var_dec | |].
apply Mem_find_var in m; destruct m; destruct H1;
rewrite H1; apply find_var_Mem in H1;
rewrite closed_subst_w_Hyb_bound with (n:=0); auto;
try omega; apply H with v x; auto.
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

Theorem red_theorem:
forall G Gamma M A w,
  lc_t_Hyb M ->
  lc_w_Hyb M ->
  G |= (w, Gamma) |- M ::: A ->
  forall L W,
    OkL L nil ->
    concat (Gamma::(map snd_ G)) *=* map fst_ L ->
    (forall a b c, Mem (a,b,c) L -> lc_t_Hyb c) ->
    (forall a b c, Mem (a,b,c) L -> lc_w_Hyb c) ->
    (forall a b c, Mem (a,b,c) L -> Red c b) ->
    Red (SL L W M) A.
intros G Gamma M A w LC_t LC_w HT.
remember (w, Gamma) as Ctx; generalize dependent w;
generalize dependent Gamma.
induction HT; intros; inversion HeqCtx; subst.
(* hyp *)
inversion LC_t; subst; try omega;
apply SL_hyp with G Gamma0 w0; auto;
constructor; auto.
(* lam *)
unfold open_t_Hyb in *;
assert (exists x, x \notin L \u free_vars_Hyb (SL L0 W M) \u
       from_list (map fst_ (map fst_ L0)) \u FV_L L0) by apply Fresh;
destruct H5.
assert (forall V, Red V A -> lc_t_Hyb V -> lc_w_Hyb V ->
           Red (SL ((x, A, V) :: L0) W [hyp_Hyb (fte x) // bte 0]M) B).
intros; apply H with ((x,A)::Gamma0) w0; auto.
apply lc_t_subst_Hyb; [ constructor | inversion LC_t]; auto.
apply lc_w_subst_t_Hyb; [ constructor | inversion LC_w]; auto.
constructor; [rewrite Mem_nil_eq; tauto | apply OkL_fresh]; auto;
rewrite notin_union; rewrite from_list_nil; split; auto.
rew_map in *; simpl; rewrite <-  H1; rew_concat; auto.
intros; rewrite Mem_cons_eq in *; destruct H9.
inversion H9; subst; auto.
apply H2 with a b; auto.
intros; rewrite Mem_cons_eq in *; destruct H9.
inversion H9; subst; auto.
apply H3 with a b; auto.
intros; rewrite Mem_cons_eq in *; destruct H9.
inversion H9; subst; auto.
eapply H4; eauto.
simpl in *. intros. apply property_3.
constructor; auto; constructor; apply lc_SL; auto; inversion LC_t; auto.
constructor.
intros; inversion H7; subst.
unfold open_t_Hyb in *.
rewrite subst_t_Hyb_neutral_free with (v:=x); auto.
replace ([N // fte x]([hyp_Hyb (fte x) // bte 0](SL L0 W M))) with
  (SL ((x, A, N)::L0) W [hyp_Hyb (fte x) // bte 0] M).
apply H6; auto.
rewrite SL_bte_subst; auto; [ | apply notin_Mem; auto].
rewrite SL_extend_L; auto.
apply notin_Mem; auto.
inversion HT0.
(* appl *)
simpl in *; inversion LC_t; inversion LC_w; subst;
apply IHHT1 with Gamma0 w0; auto.
apply lc_SL; auto.
apply lc_w_SL; auto.
apply IHHT2 with Gamma0 w0; auto.
(* box *)
replace (SL L0 W (box_Hyb M)) with (box_Hyb (SL L0 W M)) by (simpl; auto).
apply reducible_box.
inversion LC_t; subst; apply lc_SL; auto.
unfold open_w_Hyb in *.
assert (exists w, w \notin L \u free_worlds_Hyb (SL L0 W M) \u FW_L L0
       \u from_list (map fst_ W) \u from_list (map snd_ W))
  by apply Fresh. destruct H5.
intros.
rewrite <- subst_w_Hyb_neutral_free with (w0:=x); eauto;
rewrite SL_subst_w; auto.
replace ({{fwo w // fwo x}}(SL L0 W {{fwo x // bwo 0}}M))
        with (SL L0 ((w,x)::W) {{fwo x // bwo 0}}M).
apply H with nil x; auto.
inversion LC_t; subst; apply lc_t_subst_w_Hyb; auto.
inversion LC_w; subst; apply lc_w_subst_Hyb; auto.
rew_concat; rew_map; rewrite <- H1; rew_map; rew_concat; permut_simpl.
rewrite SL_extend_W; auto; apply notin_Mem; auto.
apply notin_Mem; auto.
(* unbox *)
simpl in *; inversion LC_t; inversion LC_w; subst;
destruct (find_world W (fwo w0)); try destruct p;
apply IHHT with Gamma0 w0; auto.
(* unbox-fetch *)
simpl in *; inversion LC_t; inversion LC_w; subst;
destruct (find_world W (fwo w)); try destruct p;
apply IHHT with Gamma w; auto.
rewrite <- H1; rew_map; rew_concat; simpl; permut_simpl;
repeat rewrite flat_map_concat; simpl;
transitivity (flat_map snd_ ((w, Gamma)::G)).
rew_flat_map; auto. apply flat_map_PPermut_Hyb; rewrite <- H.
PPermut_Hyb_simpl.
rewrite <- H1; rew_map; rew_concat; simpl; permut_simpl;
repeat rewrite flat_map_concat; simpl;
transitivity (flat_map snd_ ((w, Gamma)::G)).
rew_flat_map; auto. apply flat_map_PPermut_Hyb; rewrite <- H.
PPermut_Hyb_simpl.
Qed.

Lemma lc_t_n_Hyb_subst_t:
forall N M n,
lc_t_n_Hyb n M ->
lc_t_n_Hyb n (subst_t_Hyb M (bte n) N) ->
lc_t_n_Hyb (S n) N.
induction N; intros; simpl in *; try destruct v; constructor;
repeat case_if; try inversion H1; subst; try omega;
inversion H0; subst; eauto.
apply IHN with (M:=M); eauto; apply closed_t_succ; auto.
Qed.

Theorem termination_theorem:
forall G M A w,
  emptyEquiv_Hyb G |= (w, nil) |- M ::: A ->
  WHT M.
intros; apply property_1 with A.
apply types_Hyb_lc_t_Hyb in H; auto.
apply types_Hyb_lc_w_Hyb in H; auto.
apply red_theorem with (L:=nil) (W:=nil) in H.
  rewrite SL_nil in H; auto.
  apply types_Hyb_lc_t_Hyb in H; auto.
  apply types_Hyb_lc_w_Hyb in H; auto.
  constructor.
  rew_concat; rew_map; clear H M A.
  induction G; simpl; rew_concat; auto; destruct a; auto.
  intros; rewrite Mem_nil_eq in *; contradiction.
  intros; rewrite Mem_nil_eq in *; contradiction.
  intros; rewrite Mem_nil_eq in *; contradiction.
Qed.