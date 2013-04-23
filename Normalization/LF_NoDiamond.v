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
unfold ok_Bg_LF in *.
apply ok_LF_Mem_Mem_eq' with (concat (Gamma::G)) v0; auto;
[rew_concat; rewrite Mem_app_or_eq; left; auto | ].
apply Mem_permut with (l:=(v0,t0) :: map fst_ L); [symmetry; auto |
apply Mem_here].
subst; apply H0 with v0; apply Mem_here.
assert (concat (Gamma :: G) *=* (v0, t0) :: map fst_ L) by auto;
symmetry in H; apply permut_split_head in H;
destruct H as (hd, (tl, H)).
destruct Mem_concat_mem_elem with (e:=(v0, t0)) (G:=Gamma::G).
apply Mem_permut with (l:=(v0,t0) :: map fst_ L); [symmetry; auto |];
apply Mem_here. destruct H4.
apply Mem_split in H4.
apply Mem_split in H6.
destruct H6 as (l0, (l1,H6)).
destruct H4 as (G0, (G1, H4)); subst.
destruct G0; rew_app in *.
inversion H4; subst. apply IHL with G1 (l0++l1).
rew_concat in *.
apply permut_cons_inv with (a:=(v0,t0)).
rewrite <- H3. permut_simpl.
intros; apply H0 with a; rewrite Mem_cons_eq; right; auto.
constructor.
eapply ok_Bg_LF_permut_first_tail in Ok; eauto; permut_simpl.
rewrite Mem_app_or_eq in *; destruct H5; auto; rewrite Mem_cons_eq in *;
destruct H5; auto; inversion H5; subst; elim H2; auto.
inversion H4; subst.
apply IHL with (G0 ++ (l0 ++ l1) :: G1) c.
rew_concat in *. apply permut_cons_inv with (a:=(v0,t0)).
rewrite <- H3. permut_simpl.
intros; apply H0 with a; rewrite Mem_cons_eq; right; auto.
constructor; auto.
assert (c :: G0 ++ (l0 ++ (v0, t0) :: l1) :: G1 ~=~
        ((l0++(v0, t0) :: l1) :: c :: G0 ++ G1)).
PPermut_LF_simpl; constructor; auto; permut_simpl.
rewrite H6 in Ok.
eapply ok_Bg_LF_permut_first_tail with (x:=v0)(A:=t0) (C':=l0++l1)in Ok; eauto.
Focus 2. permut_simpl.
apply ok_Bg_LF_PPermut with (G:=(l0 ++ l1) :: c :: G0 ++ G1); auto;
PPermut_LF_simpl.
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

Lemma SL_nil:
forall M,
  SL nil M = M.
induction M; intros; simpl in *;
try erewrite IHM || (erewrite IHM1; erewrite IHM2); eauto.
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
unfold open_LF in *;
assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u
       from_list (map fst_ (map fst_ L0)) \u FV_L L0) by apply Fresh;
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
simpl in *; intros; apply property_3.
constructor; auto; constructor; apply lc_SL; auto; inversion LC; auto.
constructor.
intros; inversion H6; subst; [ | inversion H12];
rewrite subst_t_neutral_free_LF with (v:=x); auto.
replace ([N // fte x]([hyp_LF (fte x) // bte 0](SL L0 M))) with
  (SL ((x, A, N)::L0) [hyp_LF (fte x) // bte 0]M).
apply H5; auto.
rewrite SL_bte_subst; auto; [ | apply notin_Mem; auto].
rewrite SL_extend; auto; apply notin_Mem; auto.
(* appl *)
simpl in *; inversion LC; subst; apply IHHT1; auto; apply lc_SL; auto.
(* box *)
simpl in *; inversion LC; subst; apply property_3.
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

Theorem SN_Lang:
forall G M A,
  emptyEquiv_LF G |= nil |- M ::: A ->
  SN M.
intros; apply property_1 with A.
apply types_LF_lc_t_LF in H; auto.
apply main_theorem with (L:=nil) in H.
rewrite SL_nil in H; auto.
apply types_LF_lc_t_LF in H; auto.
rew_concat; rew_map; clear H M A.
induction G; simpl; rew_concat; auto.
intros; rewrite Mem_nil_eq in *; contradiction.
intros; rewrite Mem_nil_eq in *; contradiction.
Qed.