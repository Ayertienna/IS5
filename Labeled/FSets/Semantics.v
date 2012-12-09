Add LoadPath "../..".
Require Import Syntax.
Require Import Substitution.
Require Import FSets.
Require Import Arith.
Require Import Relations.

Require Import LibTactics. (* case_if *)

Open Scope labeled_is5_scope.
Open Scope is5_scope.

Global Reserved Notation " Omega ';' Gamma '|-' M ':::' A '@' w " (at level 70).

Definition Context_L := list (ty * vwo).

Inductive types_L : worlds_L -> Context_L -> te_L -> ty -> var -> Prop :=
 | t_hyp_L: forall A w_n Gamma Omega v_n
   (Old: w_n \in Omega)
   (H_hyp: nth_error Gamma v_n = Some (A, fwo w_n)),
     Omega; Gamma |- hyp_L v_n ::: A@w_n
 | t_lam_L: forall A A' w Gamma Omega M
   (H_lam: Omega; (A, fwo w)::Gamma |- M:::A'@w),
     Omega; Gamma |- lam_L A M ::: A ---> A' @ w
 | t_appl_L: forall A A' w Gamma Omega M N
   (H_appl1: Omega; Gamma |- N ::: A'@w)
   (H_appl2: Omega; Gamma |- M ::: A' ---> A @ w),
     Omega; Gamma |- appl_L M N ::: A@w
 | t_box_L: forall L A w Gamma Omega M
   (Old: w \in Omega)
   (HT: forall w', w' \notin L ->
     \{w'} \u Omega; Gamma |- M^(fwo w')::: A @ w'),
     Omega; Gamma |- box_L M ::: [*]A @  w
 | t_unbox_L: forall A w Gamma Omega M
   (H_unbox: Omega; Gamma |- M ::: [*]A@w),
     Omega; Gamma |- unbox_L M ::: A @ w
 | t_get_L: forall A w w' Gamma Omega M
   (New: w \in Omega)
   (H_get: Omega; Gamma |- M ::: <*>A@w'),
     Omega; Gamma |- get_L (fwo w') M ::: <*>A@w
 | t_letdia_L: forall L A w B Gamma Omega M N
   (Old: w \in Omega)
   (H_letdia: Omega; Gamma |- M ::: <*>A@w)
   (HT: forall w', w' \notin L ->
     \{w'} \u Omega; (A, fwo w')::Gamma |- N^(fwo w'):::B@w),
     Omega; Gamma |- letdia_L M N ::: B@w
 | t_here_L: forall A w Gamma Omega M
   (H_here: Omega; Gamma |- M ::: A@w),
     Omega; Gamma |- here_L M ::: <*>A@w
 | t_fetch_L: forall A w w' Gamma Omega M
   (New: w \in Omega)
   (H_fetch: Omega; Gamma |- M ::: [*]A@w'),
     Omega; Gamma |- fetch_L (fwo w') M ::: [*]A@w
 where " Omega ';' Gamma '|-' M ':::' A '@' w " :=
 (types_L Omega Gamma M A w) : labeled_is5_scope.

Fixpoint subst_typing Omega L D : Prop :=
match L, D with
| nil, nil => True
| M::L', (A,fwo w)::D' => Omega; nil |- M ::: A@w /\ (subst_typing Omega L' D')
| _, _ => False
end.

Global Reserved Notation " M |-> N " (at level 70).

Inductive value_L: te_L -> Prop :=
| val_L_lam: forall A M, value_L (lam_L A M)
| val_L_box: forall M, value_L (box_L M)
| val_L_here: forall M (HT: value_L M), value_L (here_L M)
.

Inductive step_LF: te_L*vwo -> te_L*vwo -> Prop :=
| red_appl_lam_L: forall A M N w,
   lc_w M -> lc_w N ->
   (appl_L (lam_L A M) N, w) |-> ([N//0]M, w)
| red_unbox_box_L: forall M w,
   lc_w_n M 1 ->
   (unbox_L (box_L M), w) |-> (M^w, w)
| red_letdia_here_L: forall M N w (HVal: value_L M),
   lc_w M -> lc_w_n N 1 ->
   (letdia_L (here_L M) N, w) |-> ([M//0](N^w), w)
| red_appl_L: forall M N M' w (HRed: (M, w) |-> (M', w)),
   lc_w M -> lc_w N ->
   (appl_L M N, w) |-> (appl_L M' N, w)
| red_unbox_L: forall M M' w (HRed: (M, w) |-> (M', w)),
   lc_w M ->
   (unbox_L M, w) |-> (unbox_L M', w)
| red_fetch_L: forall M M' w w'  (HRed: (M, w) |-> (M', w)),
   lc_w M ->
   (fetch_L w M, w') |-> (fetch_L w M', w')
| red_fetch_val_L: forall w M w' (HVal: value_L M),
   lc_w M ->
   (fetch_L w M, w') |-> ({{w'//w}}M, w')
| red_here_L: forall N N' w (HRed: (N, w) |-> (N',w)),
   lc_w N ->
   (here_L N, w) |-> (here_L N', w)
| red_letdia_L: forall M M' N w (HRed: (M, w) |-> (M', w)),
   lc_w M -> lc_w_n N 1 ->
   (letdia_L M N, w) |-> (letdia_L M' N, w)
| red_get_L: forall w M M' w' (HRed: (M, w) |-> (M', w)),
   lc_w M ->
   (get_L w M, w') |-> (get_L w M', w')
| red_get_val_L: forall w M w' (HVal: value_L M),
   lc_w M ->
   (get_L w (here_L M), w') |-> (here_L {{w'//w}}M, w')
where " M |-> N " := (step_LF M N ) : labeled_is5_scope.

Section Lemmas.

Lemma closed_step_subst_term:
forall M N k l,
  lc_w_n M l ->
  lc_w_n N l ->
  lc_w_n  [N // k] M l.
induction M; intros; simpl in *;
repeat case_if; auto;
try constructor;
inversion H; subst;
try apply IHM; auto;
try apply IHM1; auto;
try apply IHM2; auto;
try apply closed_w_succ; auto;
inversion H; subst;
constructor; apply IHM; auto.
Qed.

Lemma closed_step_renaming_world:
forall M n w w',
  lc_w_n M n ->
  lc_w_n ({{fwo w//fwo w'}} M) n.
induction M; intros; inversion H; subst; simpl;
auto;
repeat case_if;
try constructor;
try eapply IHM; eauto.
Qed.

Lemma closed_step_propag:
forall M N w,
  lc_w M ->
  (M, fwo w) |-> (N, fwo w) ->
  lc_w N.
induction M; intros;
inversion H0; subst.
apply closed_step_subst_term; auto.
constructor; auto; eapply IHM1; eauto.
apply closed_step_opening; auto.
constructor; eapply IHM; eauto.
inversion H; subst; constructor;
eapply IHM; eauto.
constructor; inversion H; subst;
apply closed_step_renaming_world; auto.
apply closed_step_subst_term; auto;
apply closed_step_opening; auto.
constructor; auto; eapply IHM1; eauto.
constructor; auto; eapply IHM; eauto.
inversion H; subst; constructor;
eapply IHM; eauto.
inversion H; subst;
apply closed_step_renaming_world; auto.
Qed.

Lemma Weakening:
forall Omega Gamma Delta M A w
  (HT: Omega; Gamma |- M ::: A@w),
  Omega; Gamma ++ Delta |- M ::: A@w.
intros; induction HT; eauto using types_L.
(* t_hyp *)
constructor; [apply Old | generalize dependent v_n];
induction Gamma; destruct v_n; intros; simpl in H_hyp; simpl; try discriminate;
[ | apply IHGamma]; apply H_hyp.
Qed.


Lemma WorldWeakening:
forall Omega Gamma M A w w'
  (HT: Omega; Gamma |- M ::: A @ w),
  \{w'} \u Omega; Gamma |- M ::: A @ w.
intros; induction HT; eauto using types_L;
try (constructor; [rewrite in_union; right | ]; assumption).
apply t_box_L with (L:=L).
  rewrite in_union; right; assumption.
  intros; rewrite union_comm_assoc; apply H; assumption.
apply t_letdia_L with (L:=L) (A:=A).
  rewrite in_union; right; assumption.
  assumption.
  intros; rewrite union_comm_assoc; apply H; assumption.
Qed.

Lemma subst_t_type_preserv_end:
forall Omega Delta  M N A B w w'
  (HT1: Omega; nil |- M ::: A @ w')
  (HT2: Omega; Delta ++ (A, fwo w')::nil |- N ::: B @ w)
  (HT_lc: lc_w M),
  Omega; Delta|- [M // length Delta]N ::: B @ w.
intros;
remember (Delta ++ (A, fwo w')::nil) as Delta';
generalize dependent Delta;
induction HT2;
intros; simpl in *; subst; simpl;
eauto using types_L.
(* hyp *)
destruct (eq_nat_dec (length Delta) v_n); subst.
(* length Delta = v_n *)
assert ((A, w') = (A0, w_n)).
induction Delta.
  (* nil *)
  simpl in *;
  inversion H_hyp; inversion H_hyp; subst; reflexivity.
  (* a:: Delta *)
  simpl in *.
  apply IHDelta.
    assumption.
    inversion H; subst;
    replace Delta with (nil++Delta) by reflexivity;
    apply Weakening; assumption.
(* length Delta <> v_n *)
apply t_hyp_L; try assumption.
generalize dependent v_n;
induction Delta; simpl in *; intros.
  (* nil *)
  destruct v_n.
    absurd (0<>0); auto.
    destruct v_n; simpl in H_hyp; discriminate.
  (* a::Delta *)
  destruct v_n.
    simpl in *; assumption.
    simpl in *; apply IHDelta; auto.
(* lam *)
apply t_lam_L;
apply IHHT2;
auto.
(* box *)
apply t_box_L with (L:=L); intros.
assumption.
unfold open_w; rewrite subst_order_irrelevant.
apply H.
  assumption.
  apply WorldWeakening; assumption.
  reflexivity.
  assumption.
(* letdia *)
apply t_letdia_L with (A:=A0)(L:=L); intros.
assumption.
apply IHHT2; tauto.
unfold open_w; rewrite subst_order_irrelevant.
apply H.
  assumption.
  apply WorldWeakening; assumption.
  reflexivity.
  assumption.
Qed.


Lemma subst_t_type_preserv:
forall L Delta Omega Gamma N A w
  (HT1: subst_typing Omega L Delta)
  (HT2: Omega; Gamma ++ Delta |- N ::: A @ w)
  (HT_lc: forall M, In M L -> lc_w M),
  Omega; Gamma |- subst_list L (length Gamma) N ::: A @ w.
induction L; destruct Delta; simpl in *; intros; try contradiction.
replace Gamma with (Gamma ++ nil) by (symmetry; apply app_nil_end);
assumption.
destruct p; destruct v; destruct HT1;
apply subst_t_type_preserv_end with (A:=t)(w':=v); auto;
replace (S(length Gamma)) with (length(Gamma ++ (t, fwo v)::nil));
[apply IHL with (Delta:=Delta); try auto | ];
[rewrite <- app_assoc; simpl; assumption |
 rewrite app_length; apply plus_comm].
Qed.


Fixpoint rename_world_context (w:vwo) (w':vwo) (Gamma: Context_L) : Context_L:=
match Gamma with
| nil => @nil (ty*vwo)
| (A,w0) :: Gamma' => let w_res := if (eq_vwo_dec w0 w') then w else w0 in
                      (A, w_res) :: rename_world_context w w' Gamma'
end.

Lemma typing_renaming:
forall Gamma n A w w'
  (HT: nth_error Gamma n = Some (A,w)),
  nth_error (rename_world_context w' w Gamma) n = Some (A, w').
intros;
generalize dependent n;
induction Gamma; intros.
destruct n; simpl in *; discriminate.
destruct a; simpl in *; induction n; simpl in *.
inversion HT; subst;
destruct (eq_vwo_dec w w);
[ | elim n]; reflexivity.
apply IHGamma;
assumption.
Qed.

Lemma typing_no_renaming:
forall Gamma n A w w' w''
  (HT: nth_error Gamma n = Some (A, w''))
  (Neq: w <> w''),
  nth_error (rename_world_context w' w Gamma) n = Some (A, w'').
intros; generalize dependent n; induction Gamma; intros.
destruct n; simpl in *; discriminate.
destruct a; induction n;
simpl in *; inversion HT.
  subst; destruct (eq_vwo_dec w'' w).
    elim Neq; symmetry; assumption.
    reflexivity.
  replace (nth_error Gamma n) with (Some (A, w''));
  apply IHGamma; assumption.
Qed.

Lemma rename_w_type_preserv:
forall Omega Gamma M A w w' w'' w'''
  (Old: w' \in Omega)
  (New: w''' = if eq_var_dec w'' w then w' else w'')
  (HT: \{w} \u Omega; Gamma |- M ::: A @ w''),
  Omega; (rename_world_context (fwo w') (fwo w) Gamma) |-
    {{fwo w'//fwo w}}M ::: A @ w'''.
intros;
remember (\{w} \u Omega) as Omega';
generalize dependent Omega;
generalize dependent w''';
generalize dependent w';
induction HT; intros; simpl in *.
(* hyp *)
destruct (eq_var_dec w_n w); subst;
constructor; auto.
apply typing_renaming; assumption.
rewrite in_union in Old; destruct Old; auto;
  apply notin_singleton in n; contradiction.
apply typing_no_renaming; auto;
  intro; inversion H; subst; elim n; reflexivity.
(* lam *)
constructor;
destruct (eq_var_dec w0 w); subst.
(* w0 = w *)
replace ((A, fwo w') :: rename_world_context (fwo w') (fwo w) Gamma)
   with (rename_world_context (fwo w') (fwo w) ((A, fwo w) :: Gamma)).
apply IHHT; auto.
simpl; destruct (eq_vwo_dec (fwo w) (fwo w)); [|elim n]; reflexivity.
(* w0 <> w *)
replace ((A, fwo w0) :: rename_world_context (fwo w') (fwo w) Gamma)
   with (rename_world_context (fwo w') (fwo w) ((A, fwo w0) :: Gamma)).
apply IHHT; auto.
simpl; destruct (eq_vwo_dec (fwo w0) (fwo w)).
  inversion e; elim n; assumption.
  reflexivity.
(* appl *)
apply t_appl_L with (A':=A');
[apply IHHT1 | apply IHHT2]; assumption.
(* box *)
apply t_box_L with (L:=\{w} \u L).
destruct (eq_var_dec w0 w); subst.
  assumption.
  rewrite in_union in Old; destruct Old.
    apply notin_singleton in n; contradiction.
    assumption.
intros; apply notin_union_r in H0;
destruct H0; unfold open_w in *;
replace ({{fwo w'0//bwo 0}}({{fwo w'//fwo w}}M))
   with ({{fwo w'//fwo w}}({{fwo w'0//bwo 0}}M)).
apply H.
  assumption.
  assert (w'0 <> w).
    intro; subst; elim H0; apply in_singleton_self.
  destruct (eq_var_dec w'0 w).
    elim H2; assumption.
    reflexivity.
  rewrite in_union; right; assumption.
  subst; rewrite union_comm_assoc; reflexivity.
apply subst_w_comm; intro;
apply notin_singleton in H0;
elim H0; symmetry; assumption.
(* unbox *)
constructor; apply IHHT; assumption.
(* get *)
repeat case_if; subst; constructor; eauto.
rewrite in_union in New; destruct New;
[apply notin_singleton in H0; contradiction | assumption].
rewrite in_union in New; destruct New;
[apply notin_singleton in H0; contradiction | assumption].
(* letdia *)
apply t_letdia_L with (L:=\{w} \u L) (A:=A);
repeat case_if; subst; eauto.
rewrite in_union in Old; destruct Old;
[apply notin_singleton in H0; contradiction | assumption].
intros; apply notin_union in H0; destruct H0;
replace ({{fwo w' // fwo w}}N ^ fwo w'0) with
  ({{fwo w' // fwo w}}(N ^ fwo w'0)) by
  (unfold open_w; apply subst_w_comm; auto);
replace ((A, fwo w'0) :: rename_world_context (fwo w') (fwo w) Gamma) with
  (rename_world_context (fwo w') (fwo w) ((A, fwo w'0) :: Gamma)) by
  (simpl; case_if;
   [inversion H2; subst; apply notin_singleton in H0; elim H0 | ]; auto);
apply H; auto;
[rewrite in_union; right; assumption | apply union_comm_assoc].
intros; apply notin_union in H1; destruct H1;
replace ({{fwo w' // fwo w}}N ^ fwo w'0) with
  ({{fwo w' // fwo w}}(N ^ fwo w'0)) by
  (unfold open_w; apply subst_w_comm; auto);
replace ((A, fwo w'0) :: rename_world_context (fwo w') (fwo w) Gamma) with
  (rename_world_context (fwo w') (fwo w) ((A, fwo w'0) :: Gamma)) by
  (simpl; case_if;
   [inversion H3; subst; apply notin_singleton in H1; elim H1 | ]; auto);
apply H; auto;
[rewrite in_union; right; assumption | apply union_comm_assoc].
(* here *)
constructor; apply IHHT; assumption.
(* fetch *)
repeat case_if; subst;
constructor; auto;
rewrite in_union in New; destruct New; auto;
apply notin_singleton in H0; contradiction.
Qed.

Lemma Progress:
forall Omega M A w
  (H_lc: lc_w M)
  (HProgress: Omega; nil |- M ::: A@w),
  value_L M \/ exists N, (M, fwo w) |-> (N, fwo w).
induction M; intros; eauto using value_L; inversion HProgress; subst.
(* hyp *)
destruct n; discriminate.
(* appl *)
right;
inversion H_lc; subst;
destruct (IHM1 (A'--->A) w  H1 H_appl2).
  (* value M1 *)
  inversion H; subst; inversion H_appl2; subst.
    inversion H1; subst;
    eexists; apply red_appl_lam_L; auto.
  (* step *)
  destruct H as [M1']; exists (appl_L M1' M2); apply red_appl_L; auto.
(* unbox *)
right;
inversion H_lc; subst.
destruct (IHM ([*]A) w H0 H_unbox).
  (* value M *)
  inversion H; subst; inversion H_unbox; subst.
  exists (M0^(fwo w)).
  apply red_unbox_box_L.
  inversion H0; subst.
  assumption.
  (* step *)
   destruct H as [M']; exists (unbox_L M'); apply red_unbox_L; auto.
(* get *)
right;
inversion H_lc; subst.
destruct (IHM (<*>A0) w' H2 H_get).
  (* value M *)
  inversion H; subst; inversion H_get; subst.
    inversion H2; subst.
    eexists; apply red_get_val_L; assumption.
  (* step *)
  destruct H as [M']; exists (get_L (fwo w') M'); apply red_get_L; auto.
(* letdia *)
right;
inversion H_lc; subst.
destruct (IHM1 (<*>A0) w H3 H_letdia).
  (* value M1 *)
  inversion H; subst; inversion H_letdia; subst.
  inversion H3; subst.
  eexists; apply red_letdia_here_L; assumption.
  (* step *)
  destruct H as [M']; exists (letdia_L M' M2); apply red_letdia_L; auto.
(* here *)
inversion H_lc; subst.
destruct (IHM A0 w H0 H_here).
  (* value *)
  left; eauto using value_L.
  (* step *)
  right; destruct H as [M']; exists (here_L M'); apply red_here_L; auto.
(* fetch *)
right;
inversion H_lc; subst.
destruct (IHM ([*]A0) w' H2 H_fetch).
  (* value *)
  inversion H; subst; inversion H_fetch; subst.
  eexists; apply red_fetch_val_L; assumption.
  (* step *)
  destruct H as [M']; exists (fetch_L (fwo w') M'); apply red_fetch_L; auto.
Qed.

Lemma Preservation:
forall Omega M N A w w'
  (HType: Omega; nil |- M ::: A@w)
  (HStep: (M, fwo w) |-> (N,fwo w')),
  Omega; nil |- N ::: A@w'.
intros;
remember (@nil (ty*vwo)) as Gamma;
generalize dependent N;
generalize dependent w';
induction HType; intros;
inversion HStep; subst;
eauto using types_L.
(* red_appl_lam *)
inversion HType2; subst;
replace ([N//0] M0) with (subst_list (N::nil) (length (@nil (te_L*vwo))) M0)
  by auto;
apply subst_t_type_preserv with (Delta:=(A', fwo w')::nil); simpl; auto;
intros; destruct H; subst; auto; contradiction.
(* red_unbox_box *)
inversion HType; subst;
assert (exists w0, w0 \notin L \u (free_worlds M0)) by apply Fresh;
destruct H; apply notin_union in H; destruct H; unfold open_w in *.
replace ({{fwo w'//bwo 0}}M0) with
  ({{fwo w'//bwo 0}}({{bwo 0//fwo x}}({{fwo x//bwo 0}}M0))) by
  (rewrite (subst_id M0 x 0 H1); reflexivity);
rewrite subst_neutral;
replace (@nil (ty*vwo)) with
  (rename_world_context (fwo w') (fwo x) (@nil (ty*vwo))) by (simpl; auto);
[ | apply closed_step_opening]; auto;
apply rename_w_type_preserv with (w'':=x); auto; case_if; auto.
(* red_get_here *)
replace (here_L {{fwo w'0//fwo w'}}M0) with ({{fwo w'0//fwo w'}}(here_L M0))
  by auto;
replace (@nil (ty*vwo)) with (rename_world_context (fwo w'0) (fwo w') nil)
  by auto;
apply rename_w_type_preserv with (w'':=w'); [ | case_if | ]; auto;
apply WorldWeakening; assumption.
(* red_letdia_here *)
inversion HType; subst;
assert (exists w0, w0 \notin (L \u (free_worlds N)))
 by apply Fresh;
destruct H0; apply notin_union in H0; destruct H0.
replace ([M0//0](N^(fwo w'))) with
  (subst_list (M0::nil) (length (@nil (te_L*vwo))) (N^(fwo w'))).
apply subst_t_type_preserv with (Delta:=(A, fwo w')::nil); simpl; auto.
unfold open_w in *;
replace ({{fwo w'//bwo 0}}N) with
  ({{fwo w'//bwo 0}}({{bwo 0//fwo x}}({{fwo x//bwo 0}}N))).
  rewrite subst_neutral.
  replace ((A, fwo w')::nil) with
    (rename_world_context (fwo w') (fwo x) ((A,fwo x)::nil));
  [apply rename_w_type_preserv with (w'':=w') | ]; simpl; repeat case_if; auto.
  apply closed_step_opening; assumption.
  rewrite (subst_id N x 0 H1); reflexivity.
simpl; intros; destruct H3; subst;
[assumption | contradiction].
simpl; reflexivity.
(* red_fetch_val *)
replace (@nil (ty*vwo)) with (rename_world_context (fwo w'0) (fwo w') nil)
  by auto;
apply rename_w_type_preserv with (w'':=w'); repeat case_if; auto;
apply WorldWeakening; assumption.
Qed.

End Lemmas.

Close Scope labeled_is5_scope.