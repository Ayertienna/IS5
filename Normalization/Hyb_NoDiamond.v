Add LoadPath "..".
Add LoadPath "../Hybrid".
Require Import Shared.
Require Import Hybrid.

Open Scope is5_scope.
Open Scope hybrid_is5_scope.
Open Scope permut_scope.

Definition normal_form (M: te_Hyb) := value_Hyb M.

Inductive neutral_Hyb: te_Hyb -> Prop :=
| nHyp: forall n, neutral_Hyb (hyp_Hyb n)
| nAppl: forall M N, neutral_Hyb (appl_Hyb M N)
| nUnbox: forall M w, neutral_Hyb (unbox_fetch_Hyb w M)
| nHere: forall M w, neutral_Hyb M -> neutral_Hyb (get_here_Hyb w M)
| nULetdia: forall M N w, neutral_Hyb (letdia_get_Hyb w M N)
.

Lemma value_no_step:
forall M,
  value_Hyb M ->
  forall N w , ~ (M, w) |-> (N, w).
induction M; intros; intro;
try inversion H0; inversion H1; subst;
inversion H; subst; eapply IHM; eauto; try omega.
Qed.

Lemma neutral_or_value:
forall M,
  neutral_Hyb M \/ value_Hyb M.
induction M; intros;
try (destruct IHM; [left | right]; constructor; auto).
left; constructor.
right; constructor.
left; constructor.
right; constructor.
left; constructor.
left; constructor.
Qed.

Inductive SN: te_Hyb -> Prop :=
| val_SN: forall M, value_Hyb M -> SN M
| step_SN: forall M w,
             (forall N, (M , w) |-> (N, w) -> SN N) ->
             SN M.


Fixpoint Red (M: te_Hyb) (A: ty) : Prop :=
match A with
| tvar => SN M
| tarrow A1 A2 =>
    forall N
           (H_lc_t: lc_t_Hyb N)
           (H_lc_w: lc_w_Hyb N)
           (HRed: Red N A1),
      Red (appl_Hyb M N) A2
| tbox A1 => forall w',
               Red (unbox_fetch_Hyb (fwo w') M) A1
| tdia A1 => False
end.

Lemma closed_t_succ_Hyb:
forall M n,
  lc_t_n_Hyb n M -> lc_t_n_Hyb (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_Hyb.
Qed.

Lemma lc_t_subst_t_Hyb_bound:
forall M N n,
  lc_t_n_Hyb n N ->
  lc_t_n_Hyb (S n) M ->
  lc_t_n_Hyb n ([N//bte n] M).
induction M; intros; simpl in *; inversion H0; subst; repeat case_if;
try constructor; eauto.
assert (n <> v0) by (intro; subst; elim H1; auto); omega.
eapply IHM; auto; apply closed_t_succ_Hyb; auto.
eapply IHM2; auto; apply closed_t_succ_Hyb; auto.
Qed.

Lemma lc_t_subst_t_Hyb_free:
forall M N n v,
  lc_t_n_Hyb n N ->
  lc_t_n_Hyb n M ->
  lc_t_n_Hyb n ([N//fte v] M).
induction M; intros; simpl in *; inversion H0; subst; repeat case_if;
try constructor; eauto.
eapply IHM; eauto; apply closed_t_succ_Hyb; auto.
eapply IHM2; auto; apply closed_t_succ_Hyb; auto.
Qed.

Lemma lc_t_step_Hyb:
forall M N w,
  lc_t_Hyb M ->
  (M, w) |-> (N, w) ->
  lc_t_Hyb N.
intros; eapply lc_t_step_Hyb_preserv; eauto.
Qed.

Lemma SN_appl:
forall M N,
  lc_w_Hyb (appl_Hyb M N) ->
  lc_t_Hyb (appl_Hyb M N) ->
  SN (appl_Hyb M N) ->
  SN M.
intros;
remember (appl_Hyb M N) as T;
generalize dependent M;
generalize dependent N;
induction H1; intros; subst;
[ inversion H1 |
  assert (neutral_Hyb M0 \/ value_Hyb M0) by apply neutral_or_value];
destruct H3;
[ inversion H; subst; inversion H0; subst |
  constructor; auto];
apply step_SN with w; intros;
eapply H2 with (N0:=appl_Hyb N0 N) (N:=N);
constructor; eauto.
apply lc_w_step_Hyb_preserv in H4; auto.
apply lc_t_step_Hyb in H4; auto.
Qed.

Lemma SN_box:
forall M w,
  lc_w_Hyb (unbox_fetch_Hyb w M) ->
  lc_t_Hyb (unbox_fetch_Hyb w M) ->
  SN (unbox_fetch_Hyb w M) ->
  SN M.
intros; remember (unbox_fetch_Hyb w M) as T;
generalize dependent M;
generalize dependent w.
induction H1; intros; subst;
[ inversion H1 |
  assert (neutral_Hyb M0 \/ value_Hyb M0) by apply neutral_or_value];
destruct H3;
[ inversion H0; inversion H; subst | constructor; auto].
apply step_SN with (w:=fwo w2); intros.
inversion H; inversion H0; subst.
apply H2 with (N := unbox_fetch_Hyb (fwo w2) N) (w:=fwo w2); auto.
constructor; auto.
constructor; apply lc_w_step_Hyb_preserv in H4; auto.
constructor; apply lc_t_step_Hyb in H4; auto.
omega.
Qed.

(* CR 2 *)
Theorem property_2:
forall A M M'
  (HRed: Red M A)
  (H_lc_t: lc_t_Hyb M)
  (H_lc_w: lc_w_Hyb M)
  (HStep: forall w, (M, w) |-> (M', w)),
  Red M' A.
induction A; intros; simpl in *; intros.
(* base type *)
assert (exists (x: var), x \notin \{}) by apply Fresh; destruct H;
inversion HRed; subst;
[specialize HStep with (fwo x);
  apply value_no_step with (N:=M') (w:=fwo x) in H0; contradiction |
apply H0; auto].
(* arrow type *)
apply IHA2 with (M:=appl_Hyb M N); auto; constructor; auto.
(* box type *)
apply IHA with (M:=unbox_fetch_Hyb (fwo w') M); auto; constructor; auto.

auto.
Qed.

(* CR 3 *)
Theorem property_3:
forall A M
  (H_lc: lc_t_Hyb M),
  neutral_Hyb M ->
  (forall M' w, (M, fwo w) |-> (M', fwo w) ->
    Red M' A) ->
   Red M A.
assert (exists (x:var), x \notin \{}) as nn by apply Fresh; destruct nn; auto;
induction A; intros; simpl in *.
(* base type *)
intros; apply step_SN with (w:=fwo x); auto; intros;
apply H1 with x; auto.
(* arrow type *)
intros; apply IHA2; try constructor; auto; intros; simpl in *.
inversion H2; subst; inversion H0; subst; eapply H1; eauto.
(* box type *)
intros; apply IHA; try constructor; auto; intros;
inversion H2; subst; [inversion H0 | ];
apply H1 with w'; auto.

skip.

Qed.

(* CR 1 *)
Theorem property_1:
forall A M
  (H_lc_t: lc_t_Hyb M)
  (H_lc_w: lc_w_Hyb M),
  Red M A -> SN M.
assert (exists (x:var), x \notin \{}) as nn by apply Fresh; destruct nn; auto;
induction A; intros; simpl in *.
(* base type *)
auto.
(* arrow type *)
(* Create variable of type A1 *)
assert (forall x, neutral_Hyb (hyp_Hyb x)) by (intros; constructor).
assert (forall x, SN (hyp_Hyb x))
  by (intros; apply step_SN with (fwo x); intros; inversion H2).
assert (forall x, Red (hyp_Hyb (fte x)) A1).
  intros; apply property_3; auto.
  constructor.
  intros; inversion H3.
assert (forall x, Red (appl_Hyb M (hyp_Hyb (fte x))) A2).
intros; apply H0; auto; simpl; constructor.
assert (forall x, SN (appl_Hyb M (hyp_Hyb (fte x)))).
intros; eapply IHA2; eauto;
constructor; auto; constructor.
(* From strong_norm (appl_L M (hyp_L x)) w deduce strong_norm M w *)
eapply SN_appl; auto; constructor; auto; constructor.
(* box type *)
intros; apply SN_box with (fwo x).
constructor; auto.
constructor; auto.
apply IHA; [constructor | constructor | ]; auto.

contradiction.
Grab Existential Variables.
auto.
Qed.

Lemma reducible_abstraction:
forall A N B
  (lc_N: lc_t_Hyb (lam_Hyb A N))
  (HT: forall M,
    lc_t_Hyb M ->
    lc_w_Hyb M ->
    Red M A ->
    Red ([M// bte 0] N) B),
  Red (lam_Hyb A N) (A ---> B).
simpl; intros;
apply property_3;
repeat constructor; auto.
inversion lc_N; auto.
intros; inversion H; subst.
apply HT; auto.
inversion HT0.
Qed.

(*
Lemma reducible_box:
forall A M
  (lc_M: lc_t_Hyb M)
  (HT: Red M A),
  Red (box_Hyb M) ([*]A).
simpl; intros;
apply property_3;
repeat constructor; auto.
intros; inversion H; subst.
apply HT; auto.

inversion H2.
Qed.
*)

Fixpoint find_var (L: list (var * ty * te_Hyb)) (x:var) :
                     option (var * ty * te_Hyb) :=
match L with
| nil => None
| (v, A, M) :: L' =>
  if (eq_var_dec x v) then Some (v, A, M) else find_var L' x
end.

Fixpoint SL (L: list (var * ty * te_Hyb)) M :=
match M with
| hyp_Hyb (bte v) => M
| hyp_Hyb (fte v) =>
  let x := find_var L v in
  match x with
    | Some (v, A, M) => M
    | None => hyp_Hyb (fte v)
  end
| lam_Hyb A M => lam_Hyb A (SL L M)
| appl_Hyb M N => appl_Hyb (SL L M) (SL L N)
| box_Hyb M => box_Hyb (SL L M)
| unbox_fetch_Hyb w M => unbox_fetch_Hyb w (SL L M)
| get_here_Hyb w M => get_here_Hyb w (SL L M)
| letdia_get_Hyb w M N => letdia_get_Hyb w (SL L M) (SL L N)
end.

Fixpoint find_world (L: list (var * var)) (w:vwo) : vwo:=
match L with
| nil => w
| (w0, w1) :: L' =>
  if (eq_vwo_dec w (fwo w0)) then (fwo w1) else find_world L' w
end.

Fixpoint RL (L: list (var * var)) M :=
match M with
| hyp_Hyb v => M
| lam_Hyb A M => lam_Hyb A (RL L M)
| appl_Hyb M N => appl_Hyb (RL L M) (RL L N)
| box_Hyb M => box_Hyb (RL L M)
| unbox_fetch_Hyb w M =>
  let w' := find_world L w in
  unbox_fetch_Hyb w' (RL L M)
| get_here_Hyb w M =>
  let w' := find_world L w in
  get_here_Hyb w' (RL L M)
| letdia_get_Hyb w M N =>
    let w' := find_world L w in
    letdia_get_Hyb w' (RL L M) (RL L N)
end.

Lemma Mem_concat_mem_elem:
forall (G: bg_Hyb) (e:var*ty),
  Mem e (concat (map snd_ G)) ->
  exists l, Mem l (map snd_ G) /\ Mem e l.
induction G; intros; rew_map in *; rew_concat in *.
rewrite Mem_nil_eq in H; contradiction.
rewrite Mem_app_or_eq in H; destruct H.
exists (snd a); split; auto; apply Mem_here.
destruct (IHG e); auto; destruct H0; exists x; split; auto.
rewrite Mem_cons_eq; right; auto.
Qed.
(*
Lemma ok_Hyb_Mem_Mem_eq':
  forall (G : bg_Hyb)(v : var) (A B : ty),
    ok_Hyb G  ->
    Mem (v, A) (concatG -> Mem (v,B) G ->
    A = B.
induction G; intros.
rewrite Mem_nil_eq in H0; contradiction.
rewrite Mem_cons_eq in *; destruct H0; destruct H1; subst.
inversion H1; subst; auto.
inversion H; subst; apply Mem_split in H1; destruct H1 as (hd, (tl, H1));
assert (hd & (v, B) ++ tl *=* (v, B) :: hd ++ tl) by permut_simpl;
rewrite H1 in H6; apply ok_Hyb_permut with (G':= (v, B) :: hd ++ tl) in H6;
auto; inversion H6; subst; elim H8; apply Mem_here.
inversion H; subst; apply Mem_split in H0; destruct H0 as (hd, (tl, H0));
assert (hd & (v, A) ++ tl *=* (v, A) :: hd ++ tl) by permut_simpl;
rewrite H0 in H6; apply ok_Hyb_permut with (G':= (v, A) :: hd ++ tl) in H6;
auto; inversion H6; subst; elim H8; apply Mem_here.
eapply IHG; eauto.
inversion H; subst; eapply ok_Hyb_used_weakening; eauto.
Qed.
*)
Fixpoint OkL (L: list (var * ty * te_Hyb)) U :=
match L with
| nil => True
| (v, A, M) :: L' => ~ Mem v U /\ OkL L' (v::U)
end.

Lemma OkL_used_notin:
forall L U x A M,
  OkL L U ->
  Mem x U ->
  ~ Mem (x, A, M) L.
Admitted.

Lemma OkL_weaken:
forall L U w,
  OkL L (w::U) -> OkL L U.
Admitted.

Lemma Mem_Red_Hyp:
forall L v A M,
  (forall (a : var) (b : ty) (c : te_Hyb), Mem (a, b, c) L → Red c b) ->
  Mem (v, A, M) L ->
  OkL L nil ->
  SL L (hyp_Hyb (fte v)) = M.
induction L; intros; rew_map in *.
rewrite Mem_nil_eq in H0; contradiction.
destruct a; destruct p; simpl in *; case_if.
rewrite Mem_cons_eq in H0; destruct H0.
inversion H0; subst; auto.
destruct H1.
apply OkL_used_notin with (U:=v0::nil) in H0;
  [contradiction | auto | apply Mem_here ].
destruct H1.
apply IHL with A.
intros; apply H with a; rewrite Mem_cons_eq; right; auto.
rewrite Mem_cons_eq in H0; destruct H0; auto; inversion H0; subst;
elim H2; auto.
apply OkL_weaken in H3; auto.
Qed.

Lemma SL_hyp:
  forall L G Gamma w v A,
  OkL L nil ->
  concat (Gamma::(map snd_ G)) *=* map fst_ L ->
  (forall a b c, Mem (a, b, c) L -> Red c b) ->
  G |= (w, Gamma) |- hyp_Hyb (fte v) ::: A ->
  Red (SL L (hyp_Hyb (fte v))) A.
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
apply Mem_Red_Hyp in H4; auto;
rewrite H4; apply H1 with v; auto.
Qed.

Lemma closed_t_succ:
forall M n,
  lc_t_n_Hyb n M -> lc_t_n_Hyb (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_Hyb.
Qed.

Lemma closed_t_addition:
forall M n m,
  lc_t_n_Hyb n M -> lc_t_n_Hyb (n + m) M.
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n + S m) with (S (n+m)) by auto] ;
try apply closed_t_succ;
assumption.
Qed.

Lemma SL_nil:
forall M,
  SL nil M = M.
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
forall M L n,
  lc_t_n_Hyb n M ->
  (forall a b c, Mem (a,b,c) L -> lc_t_Hyb c) ->
  lc_t_n_Hyb n (SL L M).
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
inversion H; subst; constructor; [apply IHM2 | apply IHM1]; auto.
Qed.

Lemma lc_w_SL:
forall M L n,
  lc_w_n_Hyb n M ->
  (forall a b c, Mem (a,b,c) L -> lc_w_Hyb c) ->
  lc_w_n_Hyb n (SL L M).
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
inversion H; subst; constructor; try omega; auto; apply IHM; auto.
inversion H; subst; constructor; try omega; auto; apply IHM; auto.
inversion H; subst; constructor; try omega; auto.
Qed.

Lemma SL_bte_subst:
forall L0 M x k,
  ~ Mem x (map fst_ (map fst_ L0)) ->
  (forall v a m, Mem (v, a, m) L0 -> lc_t_Hyb m) ->
  [hyp_Hyb (fte x) // bte k](SL L0 M) =
  SL L0 [hyp_Hyb (fte x) // bte k]M.
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
Qed.

Fixpoint FV_L (L: list (var * ty * te_Hyb)) :=
match L with
| nil => \{}
| (v, A, M) :: L' => free_vars_Hyb M \u FV_L L'
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

Lemma SL_extend:
forall M L0 x A N,
  x \notin FV_L L0 ->
  ~Mem x (map fst_ (map fst_ L0)) ->
  SL ((x, A, N) :: L0) M =
  [N // fte x](SL L0 M).
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
Qed.

Lemma OkL_fresh:
forall L x a V,
  OkL L nil->
  x \notin FV_L L ->
  OkL ((x, a, V):: L) nil.
Admitted.

Lemma value_Hyb_rename:
forall M w0 w1,
  value_Hyb M -> value_Hyb {{fwo w0//fwo w1}}M.
intros; induction H; simpl in *; constructor; auto.
Qed.

Lemma SN_rename_w:
forall N w0 w1,
SN N -> SN {{fwo w0//fwo w1}}N.
intros; induction H.
constructor; apply value_Hyb_rename; auto.
apply step_SN with w; intros.
Admitted.

Lemma SL_subst_w:
forall M L w k,
  (forall a b c, Mem (a, b, c) L -> lc_w_Hyb c) ->
  {{w // bwo k}}(SL L M) =
  SL L {{w//bwo k}}M.
induction M; intros; simpl; auto;
try (erewrite IHM || (erewrite IHM1; try erewrite IHM2));
eauto.
destruct v; simpl; auto.
destruct (Mem_dec var (map fst_ (map fst_ L)) v).
apply eq_var_dec.
apply Mem_find_var in m; destruct m; destruct H0;
rewrite H0; apply find_var_Mem in H0;
rewrite closed_subst_w_Hyb_bound with (n:=0); auto;
try omega; apply H with v x; auto.
apply NotMem_find_var in n; rewrite n; simpl; auto.
Qed.

Theorem main_theorem:
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
    Red (SL L (RL W M)) A.
intros G Gamma M A w LC_t LC_w HT.
remember (w, Gamma) as Ctx; generalize dependent w;
generalize dependent Gamma.
induction HT; intros; inversion HeqCtx; subst.
(* hyp *)
replace (RL W (hyp_Hyb (fte v))) with (hyp_Hyb (fte v)) by (simpl; auto).
inversion LC_t; subst; try omega;
apply SL_hyp with G Gamma0 w0; auto;
constructor; auto.
(* lam *)
unfold open_t_Hyb in *;
assert (exists x, x \notin L \u free_vars_Hyb (SL L0 M) \u
       from_list (map fst_ (map fst_ L0)) \u FV_L L0) by apply Fresh;
destruct H5.
assert (forall V, Red V A -> lc_t_Hyb V -> lc_w_Hyb V ->
           Red (SL ((x, A, V) :: L0) (RL W [hyp_Hyb (fte x) // bte 0]M)) B).
intros; apply H with ((x,A)::Gamma0) w0; auto.
apply lc_t_subst_t_Hyb_bound; [ constructor | inversion LC_t]; auto.
apply lc_w_subst_t_Hyb; [ constructor | inversion LC_w]; auto.
apply OkL_fresh; auto.
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
simpl in *; intros; apply property_3.
constructor; auto; constructor; apply lc_SL; auto; inversion LC_t; auto.
Lemma RL_lc_t:
forall k M W,
  lc_t_n_Hyb k M ->
  lc_t_n_Hyb k (RL W M).
Admitted.
simpl; apply RL_lc_t; auto.
constructor.
intros; inversion H7; subst.
unfold open_t_Hyb in *.
rewrite subst_t_Hyb_neutral_free with (v:=x); auto.
replace ([N // fte x]([hyp_Hyb (fte x) // bte 0](SL L0 (RL W M)))) with
  (SL ((x, A, N)::L0) (RL W [hyp_Hyb (fte x) // bte 0] M)).
apply H6; auto.
rewrite SL_bte_subst; auto; [ | apply notin_Mem; auto].
rewrite SL_extend; auto.

apply notin_Mem; auto.
inversion HT0.
(* appl *)
simpl in *; inversion LC_t; inversion LC_w; subst;
apply IHHT1 with Gamma0 w0; auto.
apply lc_SL; auto.
apply lc_w_SL; auto.
apply IHHT2 with Gamma0 w0; auto.
(* box *)
simpl in *; inversion LC_t; inversion LC_w; subst; intros; apply property_3.
constructor; constructor; apply lc_SL; auto.
constructor.
intros; inversion H5; subst.
unfold open_w_Hyb in *;
assert (exists w, w \notin L) by apply Fresh.
destruct H6.
specialize H with x Gamma0 w0 w;
apply H with nil x  L0 in H6; auto.
Focus 4. rew_concat; rewrite <- H1; rew_map; rew_concat; simpl; auto.


rewrite <- subst_w_Hyb_neutral_free with (w0:=x).
rewrite SL_subst_w; auto.
apply H with Gamma0 x; auto.
rew_concat in *; rewrite <- H; permut_simpl.
inversion H6.
(* unbox *)
simpl in *;
inversion LC; subst; apply IHHT; auto.
(* unbox-fetch *)
simpl in *;
inversion LC; subst; apply IHHT; auto;
rewrite <- H0; apply PPermut_concat_permut; rewrite <- H; PPermut_Hyb_simpl.
Qed.

Lemma lc_t_n_Hyb_subst_t:
forall N M n,
lc_t_n_Hyb n M ->
lc_t_n_Hyb n (subst_t_Hyb M (bte n) N) ->
lc_t_n_Hyb (S n) N.
induction N; intros; simpl in *; try destruct v; constructor;
repeat case_if; try inversion H1; subst; try omega;
inversion H0; subst; eauto.
apply IHN with (M:=M); eauto; apply closed_t_succ_Hyb; auto.
Qed.

Lemma types_Hyb_lc_t_Hyb:
forall G Gamma M A,
  G |= Gamma |- M ::: A -> lc_t_Hyb M.
intros; induction H; constructor; try apply IHHT;
unfold open_Hyb in *; auto.
assert (exists x, x \notin L) by apply Fresh; destruct H1;
assert (x \notin L) by auto;
specialize H0 with x; apply H0 in H1;
apply lc_t_n_Hyb_subst_t in H0; auto; constructor.
Qed.

Theorem SN_Lang:
forall G M A,
  emptyEquiv_Hyb G |= nil |- M ::: A ->
  SN M.
intros; apply property_1 with A.
apply types_Hyb_lc_t_Hyb in H; auto.
apply main_theorem with (L:=nil) in H.
rewrite SL_nil in H; auto.
apply types_Hyb_lc_t_Hyb in H; auto.
rew_concat; rew_map; clear H M A.
induction G; simpl; rew_concat; auto.
intros; rewrite Mem_nil_eq in *; contradiction.
intros; rewrite Mem_nil_eq in *; contradiction.
Qed.