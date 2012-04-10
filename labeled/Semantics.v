Require Export Syntax.
Require Export Substitution.
Require Import FSets.

Open Scope is5_scope.

Global Reserved Notation " Omega ';' Gamma '|-' M ':::' A '@' w " (at level 70).

Inductive types : worlds -> list (ty*wo) -> te -> ty -> var -> Prop :=
 | t_hyp: forall A w_n Gamma Omega v_n
   (Old: w_n \in Omega)
   (H_hyp: nth_error Gamma v_n = Some (A, fwo w_n)),
     Omega; Gamma |- hyp v_n ::: A@w_n
 | t_lam: forall A A' w Gamma Omega M 
   (H_lam: Omega; (A, fwo w)::Gamma |- M:::A'@w),
     Omega; Gamma |- lam A M ::: A ---> A' @ w
 | t_appl: forall A A' w Gamma Omega M N
   (H_appl1: Omega; Gamma |- N ::: A'@w)
   (H_appl2: Omega; Gamma |- M ::: A' ---> A @ w),
     Omega; Gamma |- appl M N ::: A@w
 | t_box: forall L A w Gamma Omega M
   (Old: w \in Omega)
   (HT: forall w', w' \notin L -> \{w'} \u Omega; Gamma |- M^(fwo w')::: A @ w'),
     Omega; Gamma |- box M ::: [*]A @  w
 | t_unbox: forall A w Gamma Omega M
   (H_unbox: Omega; Gamma |- M ::: [*]A@w),
     Omega; Gamma |- unbox M ::: A @ w
 | t_get: forall A w w' Gamma Omega M
   (New: w \in Omega) 
   (H_get: Omega; Gamma |- M ::: <*>A@w'),
     Omega; Gamma |- get (fwo w') M ::: <*>A@w
 | t_letd: forall L A w B Gamma Omega M N
   (Old: w \in Omega)
   (H_letd: Omega; Gamma |- M ::: <*>A@w)
   (HT: forall w', w' \notin L -> 
     \{w'} \u Omega; (A, fwo w')::Gamma |- N^(fwo w'):::B@w),
     Omega; Gamma |- letd M N ::: B@w
 | t_here: forall A w Gamma Omega M
   (H_here: Omega; Gamma |- M ::: A@w),
     Omega; Gamma |- here M ::: <*>A@w
 | t_fetch: forall A w w' Gamma Omega M
   (New: w \in Omega) 
   (H_fetch: Omega; Gamma |- M ::: [*]A@w'),
     Omega; Gamma |- fetch (fwo w') M ::: [*]A@w
 where " Omega ';' Gamma '|-' M ':::' A '@' w " := (types Omega Gamma M A w) : is5_scope.

Fixpoint subst_typing Omega L D : Prop :=
match L, D with
| nil, nil => True
| M::L', (A,fwo w)::D' => Omega; nil |- M ::: A@w /\ (subst_typing Omega L' D')
| _, _ => False
end.

Global Reserved Notation " M |-> N " (at level 70).
Global Reserved Notation " M |->* N " (at level 70).

Inductive value: te -> Prop :=
| val_lam: forall A M, value (lam A M)
| val_box: forall M, value (box M)
| val_here: forall M (HT: value M), value (here M)
.

 Inductive step: te*wo -> te*wo -> Prop :=
 | red_appl_lam: forall A M N w,
   lc_w M -> lc_w N ->
   (appl (lam A M) N, w) |-> ([N//0]M, w)
 | red_unbox_box: forall M w,
   lc_w_n M 1 ->
   (unbox (box M), w) |-> (M^w, w)
 | red_letd_here: forall M N w (HVal: value M),
   lc_w M -> lc_w_n N 1 ->
   (letd (here M) N, w) |-> ([M//0](N^w), w)
 | red_appl: forall M N M' w (HRed: (M, w) |-> (M', w)),
   lc_w M -> lc_w N ->
   (appl M N, w) |-> (appl M' N, w)
 | red_unbox: forall M M' w (HRed: (M, w) |-> (M', w)),
   lc_w M ->
   (unbox M, w) |-> (unbox M', w)
 | red_fetch: forall M M' w w'  (HRed: (M, w) |-> (M', w)),
   lc_w M ->
   (fetch w M, w') |-> (fetch w M', w')
 | red_fetch_val: forall w M w' (HVal: value M),
   lc_w M ->
   (fetch w M, w') |-> ({w'//w}M, w')
 | red_here: forall N N' w (HRed: (N, w) |-> (N',w)),
   lc_w N ->
   (here N, w) |-> (here N', w)
 | red_letd: forall M M' N w (HRed: (M, w) |-> (M', w)),
   lc_w M -> lc_w_n N 1 ->
   (letd M N, w) |-> (letd M' N, w)
| red_get: forall w M M' w' (HRed: (M, w) |-> (M', w)),
   lc_w M ->
   (get w M, w') |-> (get w M', w')
| red_get_val: forall w M w' (HVal: value M),
   lc_w M ->
   (get w (here M), w') |-> (here {w'//w}M, w')
where " M |-> N " := (step M N ) : is5_scope.


Section Lemmas.

Lemma Weakening:
forall Omega Gamma Delta M A w 
  (HT: Omega; Gamma |- M ::: A@w),
  Omega; Gamma ++ Delta |- M ::: A@w.
intros; induction HT; eauto using types.
  (* t_hyp *)
  apply t_hyp. 
    apply Old.
    generalize dependent v_n.
    induction Gamma; destruct v_n; intros; simpl in H_hyp; simpl; try discriminate.
      apply H_hyp.
      apply IHGamma; apply H_hyp.
Qed.


Lemma WorldWeakening:
forall Omega Gamma M A w w'
  (HT: Omega; Gamma |- M ::: A @ w),
  \{w'} \u Omega; Gamma |- M ::: A @ w.
intros; induction HT; eauto using types.
apply t_hyp.
  rewrite in_union; right; assumption.
  assumption.
apply t_box with (L:=L).
  rewrite in_union; right; assumption.
  intros; rewrite union_comm_assoc; apply H; assumption.
apply t_get.
  rewrite in_union; right; assumption.
  assumption.
apply t_letd with (L:=L) (A:=A). 
  rewrite in_union; right; assumption.
  assumption.
  intros; rewrite union_comm_assoc; apply H; assumption.
apply t_fetch.
  rewrite in_union; right; assumption.
  assumption.
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
eauto using types.
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
apply t_hyp; try assumption.
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
apply t_lam;
apply IHHT2;
auto.
(* box *)
apply t_box with (L:=L); intros.
assumption.
unfold open_w; rewrite subst_order_irrelevant.
apply H.
  assumption.
  apply WorldWeakening. assumption.
  reflexivity.
  assumption.
(* letd *)
apply t_letd with (A:=A0)(L:=L); intros.
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
replace Gamma with (Gamma ++ nil).
  assumption.
  symmetry; apply app_nil_end.
destruct p; destruct w0; destruct HT1.
apply subst_t_type_preserv_end with (A:=t)(w':=v).
  assumption.
replace (S(length Gamma)) with (length(Gamma ++ (t, fwo v)::nil)).
apply IHL with (Delta:=Delta); try auto.
rewrite <- app_assoc; simpl; assumption.
rewrite app_length; apply plus_comm.
auto.
Qed.


Fixpoint rename_world_context (w:wo) (w':wo) (Gamma: list (ty*wo)) : list(ty*wo):=
match Gamma with
| nil => @nil (ty*wo)
| (A,w0) :: Gamma' => let w_res := if (eq_wo_dec w0 w') then w else w0 in
                      (A, w_res) :: rename_world_context w w' Gamma'
end.

Lemma typing_renaming:
forall Gamma n A w w'
  (HT: nth_error Gamma n = Some (A,w)),
  nth_error (rename_world_context w' w Gamma) n = Some (A, w').
intros.
generalize dependent n.
induction Gamma; intros.
destruct n; simpl in *; discriminate.
destruct a.
simpl in *.
induction n.
simpl in *.
inversion HT; subst.
destruct (eq_wo_dec w w).
  reflexivity.
  elim n; reflexivity.
simpl in *.
apply IHGamma.
assumption.
Qed.

Lemma typing_no_renaming:
forall Gamma n A w w' w''
  (HT: nth_error Gamma n = Some (A, w''))
  (Neq: w <> w''),
  nth_error (rename_world_context w' w Gamma) n = Some (A, w'').
intros; generalize dependent n; induction Gamma; intros.  
destruct n; simpl in *; discriminate.
destruct a. 
induction n; simpl in *;
inversion HT.
  subst; destruct (eq_wo_dec w'' w).
    elim Neq; symmetry; assumption.
    reflexivity.
  replace (nth_error Gamma n) with (Some (A, w'')). 
  apply IHGamma; assumption.
Qed.

Lemma rename_w_type_preserv:
forall Omega Gamma M A w w' w'' w'''
  (Old: w' \in Omega)
  (New: w''' = if eq_var_dec w'' w then w' else w'')
  (HT: \{w} \u Omega; Gamma |- M ::: A @ w''),
  Omega; (rename_world_context (fwo w') (fwo w) Gamma) |- {fwo w'//fwo w}M ::: A @ w'''.
intros; 
remember (\{w} \u Omega) as Omega'.
generalize dependent Omega;
generalize dependent w''';
generalize dependent w'.
induction HT; intros.
(* hyp *)
simpl.
destruct (eq_var_dec w_n w); subst;
apply t_hyp.
assumption.
apply typing_renaming; assumption.
rewrite in_union in Old; destruct Old.
  apply notin_singleton in n; contradiction.
  assumption.
apply typing_no_renaming. 
  assumption.
  intro.
  inversion H; subst; elim n; reflexivity.
(* lam *)
simpl. apply t_lam.
destruct (eq_var_dec w0 w); subst.
(* w0 = w *)
replace ((A, fwo w') :: rename_world_context (fwo w') (fwo w) Gamma) with (rename_world_context (fwo w') (fwo w) ((A, fwo w) :: Gamma)). 
apply IHHT; auto.
simpl; destruct (eq_wo_dec (fwo w) (fwo w)); [|elim n]; reflexivity.
(* w0 <> w *)
replace ((A, fwo w0) :: rename_world_context (fwo w') (fwo w) Gamma) with (rename_world_context (fwo w') (fwo w) ((A, fwo w0) :: Gamma)). 
apply IHHT; auto.
simpl. destruct (eq_wo_dec (fwo w0) (fwo w)).
  inversion e; elim n; assumption.
  reflexivity.  
(* appl *)
simpl; apply t_appl with (A':=A').
apply IHHT1; assumption.
apply IHHT2; assumption.
(* box *)
simpl; apply t_box with (L:=\{w} \u L).
destruct (eq_var_dec w0 w); subst.
  assumption.
  rewrite in_union in Old; destruct Old.
  apply notin_singleton in n; contradiction.
  assumption.
intros.
apply notin_union_r in H0.
destruct H0.
unfold open_w in *.
replace ({fwo w'0//bwo 0}({fwo w'//fwo w}M)) with ({fwo w'//fwo w}({fwo w'0//bwo 0}M)).
apply H.
assumption.
assert (w'0 <> w).
 intro. subst. elim H0. apply in_singleton_self.
destruct (eq_var_dec w'0 w).
  elim H2; assumption. 
  reflexivity.
rewrite in_union.
right; assumption.
subst. rewrite union_comm_assoc; reflexivity.
apply subst_w_comm.
intro.
apply notin_singleton in H0.
elim H0; symmetry; assumption.
(* unbox *)
simpl.
apply t_unbox.
apply IHHT; assumption.
(* get *)
simpl.
destruct (eq_wo_dec (fwo w') (fwo w));
apply t_get;
destruct (eq_var_dec w0 w); subst;
try assumption.
rewrite in_union in New; destruct New.
  apply notin_singleton in n; contradiction.
  assumption.
apply IHHT.
  inversion e; subst.
  destruct (eq_var_dec w w).
    reflexivity.
    elim n; reflexivity.
  assumption.
reflexivity.
apply IHHT.
  inversion e; subst.
  destruct (eq_var_dec w w).
    reflexivity.
    elim n0; reflexivity.
  assumption.
reflexivity.
rewrite in_union in New; destruct New.
  apply notin_singleton in n0; contradiction.
  assumption.
apply IHHT.
  destruct (eq_var_dec w' w).
    subst. elim n; reflexivity.
    reflexivity.
  assumption.
  reflexivity.
apply IHHT.
  destruct (eq_var_dec w' w).
    subst; elim n; reflexivity.
    reflexivity.
    assumption.
reflexivity.
(* letd *)
simpl. apply t_letd with (L:=\{w} \u L) (A:=A).
destruct (eq_var_dec w0 w); subst.
  assumption.
  rewrite in_union in Old.
  elim Old; intro.
    apply notin_singleton in n. contradiction.
    assumption.
apply IHHT.
  assumption.
  assumption.
  assumption.
  intros.
  apply notin_union in H0; destruct H0.
  replace ({fwo w' // fwo w}N ^ fwo w'0) with ({fwo w' // fwo w}(N ^ fwo w'0)).
  replace ((A, fwo w'0) :: rename_world_context (fwo w') (fwo w) Gamma) with (rename_world_context (fwo w') (fwo w) ((A, fwo w'0) :: Gamma)). 
  subst.
  apply H.
  assumption.
  reflexivity.
  rewrite in_union; right; assumption.
  apply union_comm_assoc.
  simpl.
  destruct (eq_wo_dec (fwo w'0) (fwo w)).
    inversion e; subst.
    apply notin_singleton in H0; elim H0; reflexivity.
    reflexivity.
  unfold open_w;
  rewrite subst_w_comm.
  reflexivity.
  intro. subst.
  apply notin_singleton in H0.
  elim H0; reflexivity.
(* here *)
simpl.
apply t_here.
apply IHHT;
assumption.
(* fetch *)
simpl.
destruct (eq_wo_dec (fwo w') (fwo w));
apply t_fetch;
destruct (eq_var_dec w0 w); subst;
try assumption.
rewrite in_union in New; destruct New.
  apply notin_singleton in n; contradiction.
  assumption.
apply IHHT.
  inversion e; subst.
  destruct (eq_var_dec w w).
    reflexivity.
    elim n; reflexivity.
  assumption.
reflexivity.
apply IHHT.
  inversion e; subst.
  destruct (eq_var_dec w w).
    reflexivity.
    elim n0; reflexivity.
  assumption.
reflexivity.
rewrite in_union in New; destruct New.
  apply notin_singleton in n0; contradiction.
  assumption.
apply IHHT.
  destruct (eq_var_dec w' w).
    subst. elim n; reflexivity.
    reflexivity.
  assumption.
  reflexivity.
apply IHHT.
  destruct (eq_var_dec w' w).
    subst; elim n; reflexivity.
    reflexivity.
    assumption.
reflexivity.
Qed.


Lemma Progress:
forall Omega M A w 
  (H_lc: lc_w M)
  (HProgress: Omega; nil |- M ::: A@w),
  value M \/ exists N, (M, fwo w) |-> (N, fwo w).
induction M; intros; eauto using value; inversion HProgress; subst.
(* hyp *)
destruct n; discriminate.
(* appl *)
right;
inversion H_lc; subst;
destruct (IHM1 (A'--->A) w  H1 H_appl2).
  (* value M1 *)
  inversion H; subst; inversion H_appl2; subst.
    inversion H1; subst;
    eexists; apply red_appl_lam; auto.
  (* step *)
  destruct H as [M1']; exists (appl M1' M2); apply red_appl; auto.
(* unbox *)
right;
inversion H_lc; subst.
destruct (IHM ([*]A) w H0 H_unbox).
  (* value M *)
  inversion H; subst; inversion H_unbox; subst.
  exists (M0^(fwo w)).
  apply red_unbox_box.
  inversion H0; subst.
  assumption.
  (* step *)
   destruct H as [M']; exists (unbox M'); apply red_unbox; auto.
(* get *)
right;
inversion H_lc; subst.
destruct (IHM (<*>A0) w' H2 H_get).
  (* value M *)
  inversion H; subst; inversion H_get; subst.
    inversion H2; subst.
    eexists; apply red_get_val; assumption.
  (* step *)
  destruct H as [M']; exists (get (fwo w') M'); apply red_get; auto.
(* letd *)
right;
inversion H_lc; subst.
destruct (IHM1 (<*>A0) w H3 H_letd).
  (* value M1 *)
  inversion H; subst; inversion H_letd; subst.
  inversion H3; subst.
  eexists; apply red_letd_here; assumption.
  (* step *)
  destruct H as [M']; exists (letd M' M2); apply red_letd; auto.
(* here *)
inversion H_lc; subst.
destruct (IHM A0 w H0 H_here).
  (* value *)
  left; eauto using value.
  (* step *)
  right; destruct H as [M']; exists (here M'); apply red_here; auto.
(* fetch *)
right;
inversion H_lc; subst.
destruct (IHM ([*]A0) w' H2 H_fetch).
  (* value *)
  inversion H; subst; inversion H_fetch; subst.
  eexists; apply red_fetch_val; assumption.
  (* step *)
  destruct H as [M']; exists (fetch (fwo w') M'); apply red_fetch; auto.
Qed.

(* TODO *)
Axiom Fresh: forall (L:fset var), exists w0, w0 \notin L.


Lemma Preservation:
forall Omega M N A w w' (HType: Omega; nil |- M ::: A@w) (HStep: (M, fwo w) |-> (N,fwo w')),
  Omega; nil |- N ::: A@w'.
intros.
remember (@nil (ty*wo)) as Gamma.
generalize dependent N.
generalize dependent w'.
induction HType; intros;
inversion HStep; subst;
eauto using types.
(* red_appl_lam *)
inversion HType2; subst;
replace ([N//0] M0) with (subst_list (N::nil) (length (@nil (te*wo))) M0) by auto;
apply subst_t_type_preserv with (Delta:=(A', fwo w')::nil).
  simpl; auto.
  simpl; assumption.
  simpl; intros. destruct H. subst. assumption. contradiction.
(* red_unbox_box *)
inversion HType; subst.
assert (exists w0, w0 \notin L \u (free_worlds M0)).
apply Fresh.
destruct H.
apply notin_union in H; destruct H.
unfold open_w in *.
replace ({fwo w'//bwo 0}M0) with ({fwo w'//bwo 0}({bwo 0//fwo x}({fwo x//bwo 0}M0))).
rewrite subst_neutral.
replace (@nil (ty*wo)) with (rename_world_context (fwo w') (fwo x) (@nil (ty*wo))).
apply rename_w_type_preserv with (w'':=x).
assumption.
destruct (eq_var_dec x x). 
  reflexivity.
  elim n; reflexivity.
apply HT.
assumption.
simpl; reflexivity.
apply closed_step_opening; assumption.
rewrite (subst_id M0 x 0 H1); reflexivity.
(* red_get_here *)
replace (here {fwo w'0//fwo w'}M0) with ({fwo w'0//fwo w'}(here M0)) by auto;
replace (@nil (ty*wo)) with (rename_world_context (fwo w'0) (fwo w') nil) by auto.
apply rename_w_type_preserv with (w'':=w').
  assumption.
  destruct (eq_var_dec w' w'). 
    reflexivity.
    elim n; reflexivity.
  apply WorldWeakening; assumption.
(* red_letd_here *)
clear H.
inversion HType; subst.
assert (exists w0, w0 \notin (L \u (free_worlds N))).
apply Fresh.
destruct H.
apply notin_union in H; destruct H.
replace ([M0//0](N^(fwo w'))) with (subst_list (M0::nil) (length (@nil (te*wo))) (N^(fwo w'))).
apply subst_t_type_preserv with (Delta:=(A, fwo w')::nil).
  simpl; auto.
  simpl.
  unfold open_w in *.
  replace ({fwo w'//bwo 0}N) with ({fwo w'//bwo 0}({bwo 0//fwo x}({fwo x//bwo 0}N))).
  rewrite subst_neutral.
  replace ((A, fwo w')::nil) with (rename_world_context (fwo w') (fwo x) ((A,fwo x)::nil)).
  apply rename_w_type_preserv with (w'':=w').
  assumption.
  destruct (eq_var_dec w' x); reflexivity.
  apply HT.
  assumption.
  simpl.
  destruct (eq_wo_dec (fwo x) (fwo x)).
    reflexivity.
    elim n; reflexivity.
    apply closed_step_opening; assumption.
  rewrite (subst_id N x 0 H0); reflexivity.
simpl; intros. destruct H1; subst.
  assumption.
  contradiction.
simpl; reflexivity.
(* red_fetch_val *)
replace (@nil (ty*wo)) with (rename_world_context (fwo w'0) (fwo w') nil) by auto.
apply rename_w_type_preserv with (w'':=w').
  assumption.
  destruct (eq_var_dec w' w').
    reflexivity.
    elim n; reflexivity.
  apply WorldWeakening; assumption.
Qed.

End Lemmas.

Close Scope is5_scope.