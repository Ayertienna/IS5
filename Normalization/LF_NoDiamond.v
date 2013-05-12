Add LoadPath "..".
Add LoadPath "../LabelFree/SingleUnbox/NoDiamond".
Require Import Shared.
Require Import LabelFreeNoDia.

Open Scope is5_scope.
Open Scope permut_scope.

(* MOVE THIS TO LANG DEF! *)

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

Lemma closed_t_succ:
forall M n,
  lc_t_n_LF n M -> lc_t_n_LF (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_LF.
Qed.

Lemma closed_t_addition:
forall M n m,
  lc_t_n_LF n M -> lc_t_n_LF (n + m) M.
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n + S m) with (S (n+m)) by auto] ;
try apply closed_t_succ;
assumption.
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
intros; induction X; constructor; try apply IHHT;
unfold open_LF in *; auto.
assert { x |  x \notin L} by apply Fresh; destruct H1;
assert (x \notin L) by auto;
specialize H0 with x; apply H0 in H1;
apply lc_t_n_LF_subst_t in H0; auto; constructor.
Qed.

Inductive neutral_LF: te_LF -> Type :=
| nHyp: forall n, neutral_LF (hyp_LF n)
| nAppl: forall M N, neutral_LF (appl_LF M N)
| nUnbox: forall M, neutral_LF (unbox_LF M)
.

Lemma neutral_or_value:
forall M,
  neutral_LF M + value_LF M.
induction M; intros;
try (destruct IHM; [left | right]; constructor; auto);
try (left; constructor);
right;
constructor.
Qed.

Lemma Mem_concat_mem_elem:
forall G (e:var*ty),
  Mem e (concat G) ->
  exists (l: ctx_LF), Mem l G /\ Mem e l.
induction G; intros; rew_concat in *.
rewrite Mem_nil_eq in H; contradiction.
rewrite Mem_app_or_eq in H; destruct H.
exists a; split; auto; apply Mem_here.
destruct (IHG e); auto; destruct H0; exists x; split; auto.
rewrite Mem_cons_eq; right; auto.
Qed.

Lemma ok_LF_Mem_Mem_eq':
  forall (G : ctx_LF)(v : var) (A B : ty),
    ok_LF G nil  ->
    Mem (v, A) G -> Mem (v,B) G ->
    A = B.
induction G; intros.
rewrite Mem_nil_eq in H0; contradiction.
rewrite Mem_cons_eq in *; destruct H0; destruct H1; subst.
inversion H1; subst; auto.
inversion H; subst; apply Mem_split in H1; destruct H1 as (hd, (tl, H1));
assert (hd & (v, B) ++ tl *=* (v, B) :: hd ++ tl) by permut_simpl;
rewrite H1 in H6; apply ok_LF_permut with (G':= (v, B) :: hd ++ tl) in H6;
auto; inversion H6; subst; elim H8; apply Mem_here.
inversion H; subst; apply Mem_split in H0; destruct H0 as (hd, (tl, H0));
assert (hd & (v, A) ++ tl *=* (v, A) :: hd ++ tl) by permut_simpl;
rewrite H0 in H6; apply ok_LF_permut with (G':= (v, A) :: hd ++ tl) in H6;
auto; inversion H6; subst; elim H8; apply Mem_here.
eapply IHG; eauto.
inversion H; subst; eapply ok_LF_used_weakening; eauto.
Qed.

Lemma eq_te_LF_dec:
forall (M1: te_LF) (M2: te_LF),
  {M1 = M2} + {M1 <> M2}.
decide equality.
apply eq_vte_dec.
apply eq_ty_dec.
Qed.

(* Termination begins here *)

Inductive WHT: te_LF -> Type :=
| val_WHT: forall M, value_LF M -> WHT M
| step_WHT: forall M, (* change this to transitive closure? *)
             (*
(forall N, M |-> N -> WHT N) ->
             WHT M. *)
              sigT (fun V => prod (value_LF V) (steps_LF M V)) -> WHT M.
(*
Lemma WHT_appl:
forall M N,
  lc_t_LF (appl_LF M N) ->
  WHT (appl_LF M N) ->
  WHT M.
intros;
remember (appl_LF M N) as T;
generalize dependent M;
generalize dependent N;
induction H0; intros; subst.
inversion v; auto.
destruct (neutral_or_value M0);
[ | constructor; auto];
apply step_WHT; intros.
apply H0 with (N0:=appl_LF N0 N) (N:=N); auto.
constructor; eauto.
inversion H; auto.
inversion H; auto.
apply lc_t_step_LF with (M:=appl_LF M0 N); auto. constructor; auto.
inversion H; auto.
inversion H; auto.
Qed.

Lemma WHT_box:
forall M,
  lc_t_LF (unbox_LF M) ->
  WHT (unbox_LF M) ->
  WHT M.
intros; remember (unbox_LF M) as T;
generalize dependent M;
induction H0; intros; subst;
[ inversion v |
  destruct (neutral_or_value M0)];
[  | constructor; auto];
apply step_WHT; intros;
apply H0 with (N := unbox_LF N).
constructor; auto; inversion H; auto.
apply lc_t_step_LF with (M:=unbox_LF M0); auto; constructor; auto;
inversion H; auto.
auto.
Qed.
*)
Fixpoint Red (M: te_LF) (A: ty) : Type :=
match A with
| tvar => WHT M
| tarrow A1 A2 =>
    prod (WHT M)
    (forall N,
       lc_t_LF N ->
       Red N A1 ->
      Red (appl_LF M N) A2)
| tbox A1 => prod (WHT M) (Red (unbox_LF M) A1)
end.

Lemma step_LF_unique:
forall M N N',
M |-> N -> M |->N' -> N = N'.
intros; generalize dependent N'; induction H; intros; inversion H0; subst;
auto. inversion H5. inversion H2. inversion H.
rewrite IHstep_LF with M'0; auto.
inversion H. rewrite IHstep_LF with M'0; auto.
Qed.

Lemma WHT_step:
forall M M',
  WHT M ->
  M |-> M' ->
  WHT M'.
intros; inversion H; subst.
apply value_no_step with (N:=M') in H1; auto; contradiction.
destruct H1 as (V, (H1, H2)).
inversion H2; subst.
apply step_LF_unique with (N':=V) in H0; subst; auto. constructor; auto.
apply step_WHT; exists V; split; auto.
apply step_LF_unique with (N':=M'0) in H0; subst; auto.
Qed.

Lemma WHT_step_back:
forall M M',
  M |-> M' ->
WHT M' -> WHT M.
intros; apply step_WHT.
inversion H0; subst.
exists M'; split; auto; constructor; auto.
destruct H1; destruct p.
exists x; split; auto; apply multi_step_LF with (M':=M'); auto.
Qed.

Hint Resolve WHT_step WHT_step_back.

(* CR 2 *)
Theorem property_2:
forall A M M'
  (HRed: Red M A)
  (H_lc_t: lc_t_LF M)
  (HStep: M |-> M'),
  Red M' A.
induction A; intros; simpl in *; intros.
(* base type *)
eauto.
(* arrow type *)
destruct HRed; split; eauto; intros.
apply IHA2 with (M:=appl_LF M N); auto.
constructor; auto.
constructor; auto.
(* box type *)
destruct HRed; split; eauto; intros.
apply IHA with (M:=unbox_LF M); auto; constructor; eauto.
Qed.

(* CR 1 *)
Theorem property_1:
forall A M
  (H_lc_t: lc_t_LF M),
  Red M A -> WHT M.
induction A; intros; simpl in *; auto;
destruct X; auto.
Qed.

(* CR 3 *)
Theorem property_3:
forall A M M'
  (H_lc: lc_t_LF M),
  M |-> M' ->
  Red M' A ->
  Red M A.
induction A; intros; simpl in *.
(* base type *)
eauto.
(* arrow type *)
destruct X; split; eauto; intros.
apply IHA2 with (appl_LF M' N); try constructor; auto; intros; simpl in *.
(* box type *)
destruct X; split; eauto; intros.
intros; apply IHA with (unbox_LF M'); try constructor; auto.
Qed.

(*
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
*)

Fixpoint find_var (L: list (var * ty * te_LF)) (x:var) :
                     option (var * ty * te_LF) :=
match L with
| nil => None
| (v, A, M) :: L' =>
  if (eq_var_dec x v) then Some (v, A, M) else find_var L' x
end.

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

Fixpoint OkL (L: list (var * ty * te_LF)) U :=
match L with
| nil => True
| (v, A, M) :: L' => ~ Mem v U /\ OkL L' (v::U)
end.

Lemma OkL_permut:
forall L U1 U2,
  U1 *=* U2 ->
  OkL L U1 -> OkL L U2.
induction L; intros; [constructor | destruct a; destruct p];
inversion H0; subst; constructor.
intro; elim H1; apply Mem_permut with (l:=U2); [symmetry | ]; auto.
apply IHL with (U1:=v::U1); auto.
Qed.

Lemma OkL_weaken:
forall L U w,
  OkL L (w::U) -> OkL L U.
induction L; intros; simpl in *; auto; destruct a; destruct p; destruct H;
split.
intro; elim H; rewrite Mem_cons_eq; right; auto.
apply IHL with w. apply OkL_permut with (U1:=v::w::U); auto; permut_simpl.
Qed.

Lemma OkL_used_notin:
forall L U x A M,
  OkL L U ->
  Mem x U ->
  ~ Mem (x, A, M) L.
induction L; intros.
rewrite Mem_nil_eq; tauto.
intro; destruct a; destruct p; rewrite Mem_cons_eq in *; inversion H; subst;
destruct H1.
inversion H1; subst; contradiction.
specialize IHL with U x A M.
apply OkL_weaken in H3; apply IHL in H3; auto.
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

Lemma Mem_find_var_type:
  forall L v A,
    OkL L nil ->
    Mem (v, A) (map fst_ L) ->
    {M | find_var L v = Some (v, A, M)}.
induction L; intros; [ rewrite Mem_nil_eq in *; contradiction | ];
destruct a; destruct p; rew_map in *; simpl in *; destruct H.
subst; apply Mem_cons_spec in H0.
case_if.
destruct H0.
inversion e; subst; exists t; auto.
destruct IHL with v0 A; auto.
apply OkL_weaken in H1; auto.
apply find_var_Mem in e.
apply OkL_used_notin with (x:=v0) (A:=A) (M:=x) in H1; [ | apply Mem_here];
contradiction.
destruct H0; [inversion e; subst; elim H2; auto | ].
apply IHL; auto; apply OkL_weaken in H1; auto.
intros; decide equality. apply eq_ty_dec. apply eq_var_dec.
Qed.

Fixpoint SL (L: list (var * ty * te_LF)) (M: te_LF) : te_LF :=
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

Lemma SL_nil:
forall M,
  SL nil M = M.
induction M; intros; simpl in *;
try erewrite IHM || (erewrite IHM1; erewrite IHM2); eauto.
destruct v; auto.
Qed.

Lemma lc_SL:
forall M L n,
  lc_t_n_LF n M ->
  (forall a b c, Mem (a,b,c) L -> lc_t_LF c) ->
  lc_t_n_LF n (SL L M).
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
Qed.

Fixpoint FV_L (L: list (var * ty * te_LF)) :=
match L with
| nil => \{}
| (v, A, M) :: L' => used_vars_te_LF M \u FV_L L'
end.

Lemma notin_FV_notin_elem:
forall x L,
  x \notin FV_L L ->
  forall a b c, Mem (a,b,c) L -> x \notin used_vars_te_LF c.
induction L; intros; simpl in *.
rewrite Mem_nil_eq in *; contradiction.
rewrite Mem_cons_eq in H0; destruct H0; [inversion H0; subst | ].
rewrite notin_union in H; destruct H; auto.
destruct a; destruct p; rewrite notin_union in H; destruct H;
apply IHL with (a:=a0) (b:=b); auto.
Qed.

Lemma SL_hyp:
forall L G Gamma v A,
  OkL L nil ->
  concat (Gamma::G) *=* map fst_ L ->
  (forall a b c, Mem (a, b, c) L -> Red c b) ->
  G |= Gamma |- hyp_LF (fte v) ::: A ->
  Red (SL L (hyp_LF (fte v))) A.
intros.
inversion X0; subst.
assert (Mem (v, A) (map fst_ L)).
  apply Mem_permut with (l:=concat (Gamma::G)); auto.
  rew_concat; rewrite Mem_app_or_eq; left; auto.
apply Mem_find_var_type in H1; auto. destruct H1.
simpl; rewrite e; apply X with v.
apply find_var_Mem; auto.
Qed.

Lemma SL_bte_subst:
forall L0 M x k,
  ~ Mem x (map fst_ (map fst_ L0)) ->
  (forall v a m, Mem (v, a, m) L0 -> lc_t_LF m) ->
  [hyp_LF (fte x) // bte k](SL L0 M) =
  SL L0 [hyp_LF (fte x) // bte k]M.
induction M; intros; simpl in *;
try rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto.
case_if; simpl.
case_if. rewrite NotMem_find_var; auto.
destruct v; simpl; repeat case_if; auto.
destruct (Mem_dec var (map fst_ (map fst_ L0)) v);
try apply eq_var_dec; [ | rewrite NotMem_find_var]; auto;
simpl; repeat case_if; auto.
apply Mem_find_var in m; destruct m as (a, (b, m)); rewrite m; simpl.
rewrite closed_subst_t_bound_LF with (n:=0); auto; try omega;
apply H0 with v a; apply find_var_Mem; auto.
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
rewrite closed_subst_t_free_LF; auto.
apply notin_FV_notin_elem with L0 v a; eauto.
apply find_var_Mem; eauto.
Qed.

Theorem main_theorem:
forall G M A,
  lc_t_LF M ->
  emptyEquiv_LF G |= nil |- M ::: A -> Red M A.
intros. remember nil as Gamma.
remember (emptyEquiv_LF G) as G'; generalize dependent G.
induction X; intros; subst.
rewrite Mem_nil_eq in H0; contradiction.
repeat constructor; intros.
apply property_3 with (M':=M ^t^ N).
Abort.

Theorem main_theorem:
forall G Gamma M A,
  lc_t_LF M ->
  G |= Gamma |- M ::: A ->
  forall L,
    OkL L nil ->
    concat(Gamma::G) *=* map fst_ L ->
    (forall a b c, Mem (a,b,c) L -> lc_t_LF c) ->
    (forall a b c, Mem (a,b,c) L -> Red c b) ->
    Red (SL L M) A.
intros G Gamma M A LC HT; induction HT; intros.
(* hyp *)
apply SL_hyp with G Gamma; auto; constructor; auto.
(* lam *)
unfold open_LF in *;
assert {x | x \notin L \u used_vars_te_LF (SL L0 M) \u
       from_list (map fst_ (map fst_ L0)) \u FV_L L0} by apply Fresh.
destruct H3.
assert (forall V, Red V A -> lc_t_LF V ->
           Red (SL ((x, A, V) :: L0) [hyp_LF (fte x) // bte 0]M) B).
intros; apply X; auto.
apply lc_t_subst_t_LF_bound; [ constructor | inversion LC]; auto.
constructor. rewrite Mem_nil_eq; tauto.
apply OkL_fresh; auto; rewrite notin_union; split; auto;
rewrite from_list_nil; auto.
rew_map in *; simpl; rewrite <-  H1; rew_concat; auto.
intros; rewrite Mem_cons_eq in *; destruct H4.
inversion H4; subst; auto.
apply H2 with a b; auto.
intros; apply Mem_cons_spec in H4. destruct H4.
inversion e; subst; auto.
apply X0 with a ; auto.
intros; destruct k; destruct p; destruct k'; destruct p; decide equality.
apply eq_te_LF_dec. destruct p; destruct a0; decide equality.
apply eq_ty_dec. apply eq_var_dec.
simpl in *; split; intros. repeat constructor.
apply property_3 with (M':=(SL L0 M) ^t^ N).
constructor; auto; constructor; apply lc_SL; auto; inversion LC; auto.
constructor.
constructor; auto. inversion LC; subst; apply lc_SL; auto.
unfold open_LF in *.
rewrite subst_t_neutral_free_LF with (v:=x); auto.
replace ([N // fte x]([hyp_LF (fte x) // bte 0](SL L0 M))) with
  (SL ((x, A, N)::L0) [hyp_LF (fte x) // bte 0]M).
apply X1; auto.
rewrite SL_bte_subst; auto; [ | apply notin_Mem; auto].
rewrite SL_extend; auto; apply notin_Mem; auto.
(* appl *)
simpl in *; apply IHHT1; auto. inversion LC; auto.
apply lc_SL; inversion LC; auto.
apply IHHT2; auto; inversion LC; subst; auto.
(* box *)
simpl in *; split. repeat constructor.
apply property_3 with (SL L M).
constructor; constructor; apply lc_SL; inversion LC; auto.
constructor.
constructor; auto; inversion LC; subst; apply lc_SL; auto.
apply IHHT; auto; rew_concat in *. inversion LC; auto.
rewrite <- H0; permut_simpl.
(* unbox *)
simpl in *; apply IHHT; auto.
inversion LC; auto.
(* unbox-fetch *)
simpl in *;apply IHHT; auto.
inversion LC; auto.
rewrite <- H0; apply PPermut_concat_permut.
transitivityP (Gamma' :: G & Gamma); PPermut_LF_simpl.
Qed.

Theorem WHT_Lang:
forall G M A,
  emptyEquiv_LF G |= nil |- M ::: A ->
  WHT M.
intros; apply property_1 with A.
apply types_LF_lc_t_LF in X; auto.
apply main_theorem with (L:=nil) in X.
rewrite SL_nil in X; auto.
apply types_LF_lc_t_LF in X; auto.
simpl; auto.
rew_concat; rew_map; clear X M A.
induction G; simpl; rew_concat; auto.
intros; rewrite Mem_nil_eq in *; contradiction.
intros; rewrite Mem_nil_eq in *; contradiction.
Qed.

Extraction "termination_LF_nodia" WHT_Lang.