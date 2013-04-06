Add LoadPath "..".
Add LoadPath "../LabelFree/SingleUnbox".
Add LoadPath "../Hybrid".

Require Import Shared.
Require Import LabelFree.
Require Import Hybrid.
Require Import Arith.
Require Import ListLib.
Require Import Setoid.

Open Scope is5_scope.
Open Scope permut_scope.
(* FIXME: There is no labelfree is5 scope *)
Open Scope hybrid_is5_scope.

Definition LF_to_Hyb_ctx (G: bg_LF) (G': bg_Hyb) :=
  map snd_ G' *=* G /\ ok_Hyb G' nil.

Lemma LF_to_Hyb_ctx_Ok:
forall G G',
  ok_Bg_LF G -> LF_to_Hyb_ctx G G' -> ok_Bg_Hyb G'.
Admitted.

Lemma LF_to_Hyb_ctx_extend_t:
forall G G' w Gamma v A,
LF_to_Hyb_ctx (((v,A)::Gamma)::G) ((w, (v,A)::Gamma)::G') ->
LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G').
Admitted.

Lemma LF_to_Hyb_ctx_extend_w:
forall G G' w,
  LF_to_Hyb_ctx (nil::G) ((w, nil)::G') ->
  LF_to_Hyb_ctx G G'.
Admitted.

Add Morphism LF_to_Hyb_ctx: LF_to_Hyb_ctx_LF.
Admitted.

Fixpoint LF_to_Hyb_ctx_fun (G: bg_LF) (U: list var) :=
match G with
| nil => nil
| Gamma :: G' =>
  let w:= var_gen (from_list U) in
  (w, Gamma) :: LF_to_Hyb_ctx_fun G' (w::U)
end.

(* For each good context from LF there is a context from Hyb that extends it *)
(* Namely the one created in LF_to_Hyb_ctx_fun *)
Lemma LF_to_Hyb_ctx_Exists:
forall Gamma G,
  ok_Bg_LF (Gamma::G) ->
  exists w' G', LF_to_Hyb_ctx (Gamma::G) ((w', Gamma)::G').
Admitted.

Inductive LF_to_Hyb_rel: (* bg_LF  -> *) ctx_LF  -> te_LF  -> ty ->
                         bg_Hyb -> var -> te_Hyb -> Prop :=

| hyp_LF_Hyb:
    forall G Gamma G' w v A,
      types_LF G Gamma (hyp_LF v) A ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma (hyp_LF v) A
                    G' w (hyp_Hyb v)

| lam_LF_Hyb:
    forall L G Gamma G' w M M' A B,
      types_LF G Gamma (lam_LF A M) (A ---> B) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      (forall v0,
         v0 \notin L ->
         LF_to_Hyb_rel ((v0, A)::Gamma) (open_LF M (hyp_LF (fte v0))) B
                       G' w
                       (M' ^t^ (hyp_Hyb (fte v0)))) ->
      LF_to_Hyb_rel Gamma (lam_LF A M) (A ---> B) G' w (lam_Hyb A M')

| appl_LF_Hyb:
    forall G Gamma G' w M1 M2 N1 N2 A B,
      types_LF G Gamma (appl_LF M1 N1) B ->
      LF_to_Hyb_rel Gamma M1 (A ---> B) G' w M2 ->
      LF_to_Hyb_rel Gamma N1 A G' w N2 ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma (appl_LF M1 N1) B G' w (appl_Hyb M2 N2)

| box_LF_Hyb:
    forall L G Gamma G' w M N A,
      types_LF G Gamma (box_LF M) ([*]A) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      (forall w0, w0 \notin L ->
        LF_to_Hyb_rel (@nil (var*ty)) M A
                      ((w,Gamma)::G') w0 (N ^w^ (fwo w0))) ->
      LF_to_Hyb_rel Gamma (box_LF M) ([*]A) G' w (box_Hyb N)

| unbox_LF_Hyb:
    forall G Gamma G' w M N A,
      types_LF G Gamma (unbox_LF M) A ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma M ([*]A) G' w N ->
      LF_to_Hyb_rel Gamma (unbox_LF M) A
                    G' w (unbox_fetch_Hyb (fwo w) N)

| unbox_fetch_LF_Hyb:
    forall G Gamma Gamma' G' w w' M N A,
      w <> w' ->
      types_LF (Gamma'::G) Gamma (unbox_LF M) A ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      LF_to_Hyb_rel Gamma' M ([*]A)
                    ((w, Gamma)::G') w' N ->
      LF_to_Hyb_rel Gamma (unbox_LF M) A
                    ((w', Gamma')::G') w (unbox_fetch_Hyb (fwo w') N)

| here_LF_Hyb:
    forall G Gamma G' w A M N,
      types_LF G Gamma (here_LF M) (<*>A) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma M A G' w N ->
      LF_to_Hyb_rel Gamma (here_LF M) (<*>A)
                    G' w (get_here_Hyb (fwo w) N)

| get_here_LF_Hyb:
    forall G Gamma Gamma' G' w w' A M N,
      w <> w' ->
      types_LF (Gamma'::G) Gamma (here_LF M) (<*>A) ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      LF_to_Hyb_rel Gamma' M A
                    ((w, Gamma)::G') w' N ->
      LF_to_Hyb_rel Gamma (here_LF M) (<*>A)
                    ((w', Gamma')::G') w (get_here_Hyb (fwo w') N)

| letdia_LF_Hyb:
    forall Lt Lw G Gamma G' w A B M1 M2 N1 N2,
      types_LF G Gamma (letdia_LF M1 N1) B ->
      LF_to_Hyb_rel Gamma M1 (<*>A) G' w M2 ->
      (forall w'0 v', w'0 \notin Lw -> v' \notin Lt ->
                     LF_to_Hyb_rel Gamma (open_LF N1 (hyp_LF (fte v'))) B
                                   ((w'0, (v', A) :: nil ) :: G') w
                                   ((N2 ^w^ fwo w'0 ) ^t^ hyp_Hyb (fte v'))) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma (letdia_LF M1 N1) B G' w
                    (letdia_get_Hyb (fwo w) M2 N2)

| letdia_get_LF_Hyb:
    forall Lt Lw G Gamma Gamma' G' w w' A B M1 M2 N1 N2,
      types_LF (Gamma'::G) Gamma (letdia_LF M1 N1) B ->
      LF_to_Hyb_rel Gamma' M1 (<*>A)
                    ((w, Gamma)::G') w' M2 ->
      (forall w'0 v', w'0 \notin Lw -> v' \notin Lt ->
         LF_to_Hyb_rel Gamma (open_LF N1 (hyp_LF (fte v'))) B
                       (((w'0, (v', A) :: nil ) :: (w', Gamma')::G'))
                       w ((N2 ^w^ fwo w'0 ) ^t^ hyp_Hyb (fte v'))) ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      LF_to_Hyb_rel Gamma (letdia_LF M1 N1) B
                    ((w', Gamma')::G') w
                    (letdia_get_Hyb (fwo w') M2 N2)
.

Lemma LF_to_Hyb_types:
forall G' Gamma M A w M',
  LF_to_Hyb_rel Gamma M A G' w M' ->
  types_Hyb G' (w, Gamma) M' A.
intros; induction H; intros.
(* hyp *)
inversion H; subst; constructor; [eapply LF_to_Hyb_ctx_Ok | ]; eauto.
(* lam *)
inversion H; subst;
apply t_lam_Hyb with (L:=L \u L0); [eapply LF_to_Hyb_ctx_Ok | ]; eauto; intros;
unfold open_t_Hyb in *; unfold open_LF in *;
apply H1; eauto.
(* appl *)
inversion H; subst; econstructor; [eapply LF_to_Hyb_ctx_Ok| | ]; eauto.
(* box *)
inversion H; subst; apply t_box_Hyb with (L:=L);
assert (PPermut_LF (G & Gamma) (Gamma :: G)) as H4 by PPermut_LF_simpl;
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') as H3 by PPermut_Hyb_simpl.
rewrite H3; eapply LF_to_Hyb_ctx_Ok; eauto; rewrite H4; auto.
intros; rewrite H3; eapply H2; eauto; rewrite <- H4; auto.
(* unbox *)
inversion H; subst.
constructor; [eapply LF_to_Hyb_ctx_Ok|] ; eauto.
constructor; auto;
eapply LF_to_Hyb_ctx_Ok; eauto;
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma::G))
       by (rewrite <- H6; PPermut_LF_simpl);
rewrite H2; auto.
(* unbox-fetch *)
inversion H0; subst.
apply t_unbox_fetch_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl;
rewrite <- H3; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H3; auto.
PPermut_Hyb_simpl.
apply t_unbox_fetch_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl.
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma :: Gamma' :: G)) by
(transitivity (G0 & Gamma0 & Gamma); [ | rewrite H7 ];
 rew_app; PPermut_LF_simpl).
rewrite H5 in Ok.
rewrite <- H3; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H3; auto.
PPermut_Hyb_simpl.
(* here *)
inversion H; subst.
constructor; [eapply LF_to_Hyb_ctx_Ok|] ; eauto.
constructor; auto;
eapply LF_to_Hyb_ctx_Ok; eauto;
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma::G))
       by (rewrite <- H7; PPermut_LF_simpl);
rewrite H2; auto.
(* get-here *)
inversion H0; subst.
apply t_get_here_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl;
rewrite <- H3; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H3; auto.
PPermut_Hyb_simpl.
apply t_get_here_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl.
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma :: Gamma' :: G)) by
(transitivity (G0 & Gamma0 & Gamma); [ | rewrite H8 ];
 rew_app; PPermut_LF_simpl).
rewrite H4 in Ok.
rewrite <- H3; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H3; auto.
PPermut_Hyb_simpl.
(* letdia *)
inversion H; subst.
econstructor; [eapply LF_to_Hyb_ctx_Ok | | intros] ; eauto.
econstructor; intros; eauto;
eapply LF_to_Hyb_ctx_Ok; eauto;
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma::G))
       by (rewrite <- H9; PPermut_LF_simpl);
rewrite H4; auto.
(* letdia-get *)
inversion H; subst.
eapply t_letdia_get_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl;
rewrite <- H4; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H4; eauto.
intros;
assert ((w'0, (v', A) :: nil) :: (w', Gamma') :: G' ~=~
        (w'0, (v', A) :: nil) :: G' & (w', Gamma')) by PPermut_Hyb_simpl;
rewrite <- H6; eauto.
PPermut_Hyb_simpl.
eapply t_letdia_get_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl.
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma :: Gamma' :: G)) by
(transitivity (G0 & Gamma0 & Gamma); [ | rewrite H9 ];
 rew_app; PPermut_LF_simpl).
rewrite H5 in Ok.
rewrite <- H4; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H4; eauto.
intros;
assert ((w'0, (v', A) :: nil) :: (w', Gamma') :: G' ~=~
        (w'0, (v', A) :: nil) :: G' & (w', Gamma')) by PPermut_Hyb_simpl;
rewrite <- H6; eauto.
PPermut_Hyb_simpl.
Qed.

Lemma LF_to_Hyb_value:
forall G' Gamma M A w M',
  LF_to_Hyb_rel Gamma M A G' w M' ->
  value_LF M -> value_Hyb M'.
intros; induction H; simpl;
inversion H0; subst; constructor; eauto.
Qed.

(* Things to be moved into language definitions *)

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma lc_w_subst_t_Hyb:
forall N M v n,
  lc_w_n_Hyb n M ->
  lc_w_n_Hyb n N ->
  lc_w_n_Hyb n (subst_t_Hyb M v N).
induction N; intros; inversion H0; subst; simpl in *; try case_if;
auto; constructor; try eapply IHN; eauto. apply closed_w_succ; auto.
eapply IHN2; [apply closed_w_succ | ]; auto.
eapply IHN2; [apply closed_w_succ | ]; auto.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma lc_w_subst_Hyb:
forall M w k,
  lc_w_n_Hyb (S k) M ->
  lc_w_n_Hyb k {{fwo w // bwo k}} M.
induction M; intros; simpl in *; repeat case_if;
inversion H; subst; try destruct w;
constructor; eauto.
destruct (eq_nat_dec m k); subst; [elim H0 |]; auto; omega.
destruct (eq_nat_dec m k); subst; [elim H0 |]; auto; omega.
destruct (eq_nat_dec m k); subst; [elim H0 |]; auto; omega.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma lc_w_subst_Hyb_same_n_fwo:
forall M w w' n,
  lc_w_n_Hyb n M ->
  lc_w_n_Hyb n {{fwo w // w'}} M.
induction M; intros; simpl in *; repeat case_if;
inversion H; subst; try destruct w;
constructor; eauto.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma lc_w_subst_Hyb_same_n_bwo:
forall M w' k n,
  lc_w_n_Hyb n M ->
  k < n ->
  lc_w_n_Hyb n {{bwo k // w'}} M.
induction M; intros; simpl in *; repeat case_if;
inversion H; subst; try destruct w'; simpl;
constructor; try (eapply IHM || eapply IHM2); try omega; auto.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma lc_w_n_Hyb_subst_t:
forall N M v n,
lc_w_n_Hyb n (subst_t_Hyb M v N) ->
lc_w_n_Hyb n N.
induction N; intros; simpl in *; try destruct v; constructor;
inversion H; subst; try eapply IHN; eauto.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma lc_w_n_Hyb_subst_w:
forall N w n,
lc_w_n_Hyb n (subst_w_Hyb (fwo w) (bwo n) N) ->
lc_w_n_Hyb (S n) N.
induction N; intros; simpl in *; try destruct v; constructor;
inversion H; subst; try eapply IHN; eauto;
repeat case_if; inversion H0; subst; try inversion H1; subst;
try omega.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Semantics *)
Lemma types_Hyb_lc_w_Hyb:
forall G Gamma M A w,
  G |= (w, Gamma) |- M ::: A -> lc_w_Hyb M.
intros; induction H; constructor; try apply IHHT;
unfold open_w_Hyb in *; unfold open_t_Hyb in *;
auto.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0; apply lc_w_n_Hyb_subst_t in H0; auto.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0; apply lc_w_n_Hyb_subst_w in H0; auto.
assert (exists x, x \notin L_t) by apply Fresh; destruct H1;
assert (exists x, x \notin L_w) by apply Fresh; destruct H2;
specialize H0 with x x0; apply H0 with (w':=x0) in H1; auto;
apply lc_w_n_Hyb_subst_t in H1; apply lc_w_n_Hyb_subst_w in H1; auto.
assert (exists x, x \notin L_t) by apply Fresh; destruct H2;
assert (exists x, x \notin L_w) by apply Fresh; destruct H3;
specialize H0 with x x0; apply H0 with (w':=x0) in H2; auto;
apply lc_w_n_Hyb_subst_t in H2; apply lc_w_n_Hyb_subst_w in H2; auto.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma subst_w_Hyb_comm2:
forall M w w' m n
  (Neq: m <> n)
  (Neq': w <> bwo m),
  {{fwo w'//bwo m }}({{w//bwo n}}M) =
  {{w//bwo n}}({{fwo w'//bwo m}}M).
induction M; intros; simpl; destruct w;
repeat case_if; subst; simpl; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
auto; intro nn; elim Neq'; inversion nn; subst; auto.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma double_subst_w_Hyb_bwo:
forall N w w' n,
 w' <> bwo n ->
 {{w // bwo n}}({{w' // bwo n}}N) = {{w' // bwo n}}N.
induction N; destruct w'; simpl in *; intros; repeat case_if;
try rewrite IHN;
try (rewrite IHN1; try rewrite IHN2); auto; intro nn; inversion nn;
subst; elim H; auto.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma subst_t_comm2_Hyb:
forall M v' m n N
  (Neq: m <> n)
  (Lc: lc_t_Hyb N),
  subst_t_Hyb N (bte m) (subst_t_Hyb (hyp_Hyb (fte v')) (bte n) M) =
  subst_t_Hyb (hyp_Hyb (fte v')) (bte n) (subst_t_Hyb N (bte m) M).
induction M; intros; subst; simpl;
repeat (case_if; subst; simpl); auto;
try rewrite IHM; eauto; try omega.
rewrite closed_subst_t_Hyb_bound with (n:=0); auto; omega.
rewrite IHM1; eauto; rewrite IHM2; eauto; omega.
rewrite IHM1; eauto; rewrite IHM2; eauto; omega.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma subst_t_comm2_LF:
forall M v' m n N
  (Neq: m <> n)
  (Lc: lc_t_LF N),
  subst_t_LF N (bte m) (subst_t_LF (hyp_LF (fte v')) (bte n) M) =
  subst_t_LF (hyp_LF (fte v')) (bte n) (subst_t_LF N (bte m) M).
induction M; intros; subst; simpl;
repeat (case_if; subst; simpl); auto;
try rewrite IHM; eauto; try omega.
rewrite closed_subst_t_bound_LF with (n:=0); auto; omega.
rewrite IHM1; eauto; rewrite IHM2; eauto; omega.
rewrite IHM1; eauto; rewrite IHM2; eauto; omega.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma reorder_subst_w_Hyb_eq:
forall M w w' w'',
  subst_w_Hyb w w' (subst_w_Hyb w w'' M) =
  subst_w_Hyb w w'' (subst_w_Hyb w w' M).
induction M; intros; simpl; repeat case_if;
try rewrite IHM;
try rewrite IHM1; try rewrite IHM2; eauto.
Qed.

(* Fixme: rename if this works and stays *)
Inductive R: te_LF -> te_Hyb -> Prop :=
| hyp_R: forall v, R (hyp_LF v) (hyp_Hyb v)
| lam_R: forall A M N, R M N -> R (lam_LF A M) (lam_Hyb A N)
| appl_R: forall M1 M2 N1 N2, R M1 N1 -> R M2 N2 ->
                              R (appl_LF M1 M2) (appl_Hyb N1 N2)
| box_R: forall M N, R M N -> R (box_LF M) (box_Hyb N)
| unbox_R: forall M N w, R M N -> R (unbox_LF M) (unbox_fetch_Hyb w N)
| here_R: forall M N w, R M N -> R (here_LF M) (get_here_Hyb w N)
| letdia_R: forall M M' N N' w, R M M' -> R N N' ->
                          R (letdia_LF M N) (letdia_get_Hyb w M' N')
.

Lemma R_subst_t:
forall M1 M2 C1 C2 v,
  R M1 M2 -> R C1 C2 -> R (subst_t_LF C1 v M1) (subst_t_Hyb C2 v M2).
induction M1; intros; inversion H; subst; simpl in *;
repeat case_if; try constructor; eauto.
Qed.

Lemma R_subst_t_rev:
forall M1 M2 v v',
  v' \notin used_vars_te_LF M1 \u free_vars_Hyb M2 ->
  R (subst_t_LF (hyp_LF (fte v')) (bte v) M1)
    (subst_t_Hyb (hyp_Hyb (fte v')) (bte v) M2) ->
  R M1 M2.
induction M1; intros; simpl in *; try case_if.
destruct M2; simpl in *; try case_if; try inversion H0; subst;
try rewrite notin_union in *;
[constructor | destruct H; rewrite notin_singleton in *; elim H2; auto].
destruct M2; simpl in *; try case_if; try inversion H0; subst;
try rewrite notin_union in *;
[destruct H; rewrite notin_singleton in *; elim H; auto | constructor].
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
eapply IHM1; eauto.
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
[eapply IHM1_1 | eapply IHM1_2]; eauto; rewrite notin_union in *; destruct H;
split; eauto.
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
eapply IHM1; eauto.
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
eapply IHM1; eauto.
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
eapply IHM1; eauto.
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
[eapply IHM1_1 | eapply IHM1_2]; eauto; rewrite notin_union in *; destruct H;
split; auto.
Qed.

Lemma R_subst_w_rev:
forall M N w w',
  R M ({{w//w'}}N) <-> R M N.
split;
generalize dependent w';
generalize dependent w;
generalize dependent N;
generalize dependent M.
induction M; intros; inversion H; destruct N; simpl in *;
inversion H2; subst; inversion H; subst; constructor; eauto.
induction M; intros; inversion H; subst; simpl in *; repeat case_if;
constructor; eauto.
Qed.

(* This simply states that LF_to_Hyb_rel is one realisation of R *)
Lemma LF_to_Hyb_rel_R:
forall M1 Gamma A G' w M2,
  LF_to_Hyb_rel Gamma M1 A G' w M2 ->
  R M1 M2.
intros; induction H; constructor; auto.
(* lam *)
assert (exists x, x\notin L \u  used_vars_te_LF M \u free_vars_Hyb M')
  by apply Fresh; destruct H3;
specialize H2 with x;
unfold open_LF in *; unfold open_t_Hyb in *; apply R_subst_t_rev in H2; auto.
(* box *)
assert (exists x, x\notin L) by apply Fresh; destruct H3;
unfold open_w_Hyb in *. eapply R_subst_w_rev; eauto.
(* letdia *)
assert (exists x, x\notin Lw) by apply Fresh.
destruct H4.
assert (exists x0, x0 \notin Lt \u used_vars_te_LF N1 \u
                              free_vars_Hyb {{fwo x // bwo 0}}N2)
  by apply Fresh; destruct H5.
specialize H2 with x x0.
unfold open_LF in *; unfold open_t_Hyb in *;
unfold open_w_Hyb in *.
apply H2 in H4; auto.
assert (R N1 ({{fwo x // bwo 0}} N2)).
apply R_subst_t_rev with (v:=0) (v':=x0); eauto;
apply R_subst_w_rev with (w:=fwo x) (w':=bwo 0).
apply R_subst_w_rev with (w:=fwo x) (w':=bwo 0); auto.
(* letdia - get *)
assert (exists x, x\notin Lw) by apply Fresh.
destruct H4.
assert (exists x0, x0 \notin Lt \u used_vars_te_LF N1 \u
                              free_vars_Hyb {{fwo x // bwo 0}}N2)
  by apply Fresh; destruct H5.
specialize H2 with x x0.
unfold open_LF in *; unfold open_t_Hyb in *;
unfold open_w_Hyb in *.
apply H2 in H4; auto.
assert (R N1 ({{fwo x // bwo 0}} N2)).
apply R_subst_t_rev with (v:=0) (v':=x0); eauto;
apply R_subst_w_rev with (w:=fwo x) (w':=bwo 0).
apply R_subst_w_rev with (w:=fwo x) (w':=bwo 0); auto.
Qed.

(*
Lemma LF_to_Hyb_subst_t:
forall Gamma C2 C1 M1 M2 v A B G' w,
  lc_t_LF C1 -> lc_t_Hyb C2 ->
  LF_to_Hyb_rel Gamma M1 A G' w M2 ->
  LF_to_Hyb_rel Gamma C1 B G' w C2 ->
  LF_to_Hyb_rel Gamma (subst_t_LF C1 (bte v) M1) A G' w ([C2//(bte v)]M2).
intros; generalize dependent C1; generalize dependent C2;
generalize dependent B. generalize dependent v.
induction H1; intros; simpl in *.
repeat case_if; [inversion H | econstructor; eauto].
econstructor; unfold open_LF in *; unfold open_t_Hyb in *.
inversion H; subst; econstructor; eauto;
intros; unfold open_LF in *; simpl.
specialize H2 with v0 (S v) B C2 C1; apply H2 with (S v) B C2 C1 in H6; auto.
rewrite <- subst_t_comm2_LF; try omega; auto.
inversion H6; subst; auto.

Lemma LF_to_Hyb_subst_t_rev:
forall Gamma C2 C1 M1 M2 k A G' w,
  LF_to_Hyb_rel Gamma (subst_t_LF C1 (bte k) M1) A G' w M2 ->
  LF_to_Hyb_rel Gamma C1 A G' w C2 ->
  exists M2',
    M2 = subst_t_Hyb C2 (bte k) M2'.
intros. induction H; simpl in *.
(* hyp *)
inversion H; subst; exists (hyp_Hyb (fte v0)); simpl; case_if; auto.
(* lam *)
assert (exists x, x \notin L) by apply Fresh; destruct H4.
destruct H3 with x; auto.
exists (lam_Hyb A

Admitted.
*)

Lemma R_lc_t:
forall M N n,
  R M N -> lc_t_n_LF n M -> lc_t_n_Hyb n N.
induction M; intros; inversion H; inversion H0; subst; constructor; auto.
Qed.

(* Alt:
forall M M' N N' w,
  R M N -> R M' N' -> step_LF M M' -> step_Hyb (N, w) (N', w).
Basically requires this relation to be a function.
** Maybe ** this would work with LF_to_Hyb_rel..
*)

Lemma R_value:
forall M N,
  R M N -> value_LF M -> value_Hyb N.
intros; induction H; simpl;
inversion H0; subst; constructor; eauto.
Qed.

Lemma R_step:
forall M M' N w,
  lc_w_Hyb N ->
  R M N -> step_LF M M' ->
  exists N', R M' N' /\ step_Hyb (N, w) (N', w).
(* ind: M *)
induction M; intros; inversion H0; inversion H1; subst.
(* appl - lam *)
inversion H4; inversion H; inversion H8; subst.
exists (subst_t_Hyb N2 (bte 0) N); split.
apply R_subst_t; auto.
constructor; try eapply R_lc_t; eauto; inversion H13; auto.
(* appl *)
inversion H; subst.
destruct IHM1 with M'0 N1 w; auto.
destruct H2.
exists (appl_Hyb x N2); split; constructor; auto;
try eapply R_lc_t; eauto.
(* unbox - box *)
inversion H; inversion H3; subst; try omega;
exists (open_w_Hyb N (w)); split;
[unfold open_w_Hyb; apply R_subst_w_rev; auto |
 constructor; try eapply R_lc_t; eauto; inversion H5; auto].
(* unbox *)
inversion H; subst; try omega;
destruct IHM with M'0 N0 (fwo w1); auto; destruct H2;
exists (unbox_fetch_Hyb (fwo w1) x); split;
constructor; auto; try eapply R_lc_t; eauto.
(* here *)
inversion H; subst; try omega;
destruct IHM with M'0 N0 (fwo w1); auto; destruct H2;
exists (get_here_Hyb (fwo w1) x); split;
constructor; auto; try eapply R_lc_t; eauto.
(* letdia-here *)
inversion H; inversion H4; subst; try omega; inversion H11; subst; try omega.
exists ((N' ^w^ (fwo w0) ) ^t^ N0); split.
unfold open_w_Hyb; unfold open_t_Hyb; eapply R_subst_t; auto;
apply R_subst_w_rev; auto.
constructor; try eapply R_lc_t; eauto; eapply R_value; eauto.
(* letdia *)
destruct w0; inversion H; subst; try omega.
destruct IHM1 with M'1 M'0 (fwo v); auto; destruct H2;
exists (letdia_get_Hyb (fwo v) x N'); split; constructor; auto;
try eapply R_lc_t; eauto.
Qed.

Lemma LF_to_Hyb_step:
forall M G' Gamma A w M' N N',
  LF_to_Hyb_rel Gamma M A G' w M' ->
  LF_to_Hyb_rel Gamma N A G' w N' ->
  step_LF M N ->
  step_Hyb (M', fwo w) (N', fwo w).
intros. generalize dependent N; generalize dependent N'.
induction H; intros.
inversion H2.
inversion H4; subst.
(* appl *)
inversion H4; subst.
inversion H0; subst.
assert (LF_to_Hyb_rel Gamma (subst_t_LF N1 (bte 0) M) B G' w N') as NN by auto.
apply LF_to_Hyb_subst_t_rev with (M1:=M) (M2:=N') (k:=0) in NN.





(* ind: M
induction M; intros; inversion H; inversion H1; subst.
(* appl_lam *)
inversion H5; subst.
*)

Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
