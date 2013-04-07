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

Lemma LF_to_Hyb_ctx_extend2_t:
forall G G' w Gamma A,
LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
forall v, v \notin \{} ->
LF_to_Hyb_ctx (((v,A)::Gamma)::G) ((w, (v,A)::Gamma)::G').
Admitted.

Lemma LF_to_Hyb_ctx_extend2_w:
forall G G',
  LF_to_Hyb_ctx G G' ->
  forall w, w \notin \{} ->
  LF_to_Hyb_ctx (nil::G) ((w, nil)::G').
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

Lemma R_lc_t:
forall M N n,
  R M N -> lc_t_n_LF n M -> lc_t_n_Hyb n N.
induction M; intros; inversion H; inversion H0; subst; constructor; auto.
Qed.

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

Lemma R_total_L:
forall M, exists N, R M N.
induction M; try destruct IHM || (destruct IHM1; destruct IHM2);
eexists; constructor; eauto.
Grab Existential Variables.
exact (bwo 0).
exact (bwo 0).
exact (bwo 0).
Qed.

Fixpoint subst_in_ctx_LF (v1: var) (v2: var) (Gamma: ctx_LF) : ctx_LF :=
match Gamma with
| nil => nil
| (v, A) :: Gamma' =>
  let v' := if (eq_var_dec v v2) then v1 else v in
  (v', A):: subst_in_ctx_LF v1 v2 Gamma'
end.

Definition subst_in_ctx_Hyb v1 v2 (Gamma: ctx_Hyb) :=
(fst_ Gamma, subst_in_ctx_LF v1 v2 (snd_ Gamma)).

Lemma LF_to_Hyb_rel_rename_vars:
forall Gamma M B G w N v,
  LF_to_Hyb_rel Gamma M B G w N ->
  forall v0 Gamma' G' M' N',
    v0 \notin \{} ->
    Gamma' = subst_in_ctx_LF v0 v Gamma ->
    G' = map (subst_in_ctx_Hyb v0 v) G ->
    M' = subst_t_LF (hyp_LF (fte v0)) (fte v) M ->
    N' = subst_t_Hyb (hyp_Hyb (fte v0)) (fte v) N ->
    LF_to_Hyb_rel Gamma' M' B G' w N'.
Admitted.

Definition subst_w_in_ctx_Hyb w1 w2 (Gamma: ctx_Hyb) :=
let w' :=  if eq_var_dec (fst_ Gamma) w2 then w1 else (fst_ Gamma)
in (w', snd_ Gamma).

Lemma LF_to_Hyb_rel_rename_worlds:
forall Gamma M B G N w w'',
  LF_to_Hyb_rel Gamma M B G w N ->
  forall w' G' N' w0,
    w' \notin \{} ->
    G' = map (subst_w_in_ctx_Hyb w' w'') G ->
    N' = subst_w_Hyb (fwo w') (fwo w'') N ->
    (w0 = if (eq_var_dec w w'') then w' else w) ->
    LF_to_Hyb_rel Gamma M B G' w0 N'.
Admitted.

Lemma LF_to_Hyb_rel_subst_t_rev:
forall N Gamma M v N' A B G w M',
  LF_to_Hyb_rel Gamma (subst_t_LF M v N) A G w N' ->
  LF_to_Hyb_rel Gamma M B G w M' ->
  exists N0,
    N' = subst_t_Hyb M' v N0.
induction N; intros; simpl in *; repeat case_if.
Admitted.

Lemma R_te_vars:
forall N1 N2,
  R N1 N2 -> used_vars_te_LF N1 = free_vars_Hyb N2.
intros; induction H; simpl in *;
try rewrite IHR || (rewrite IHR1; rewrite IHR2); eauto.
Qed.

Lemma LF_to_Hyb_rel_te_vars:
forall N1 N2 Gamma A G w,
  LF_to_Hyb_rel Gamma N1 A G w N2 ->
  used_vars_te_LF N1 = free_vars_Hyb N2.
intros; apply R_te_vars; eapply LF_to_Hyb_rel_R; eauto.
Qed.

Lemma LF_to_Hyb_rel_total_L:
forall M Gamma A G' w,
  types_LF (map snd_ G') Gamma M A ->
  LF_to_Hyb_ctx (Gamma::(map snd_ G')) ((w, Gamma)::G') ->
  exists M',
    LF_to_Hyb_rel Gamma M A G' w M'.
intros; generalize dependent w;
remember (map snd_ G') as G;
generalize dependent G';
induction H; intros; subst.
(* hyp *)
exists (hyp_Hyb (fte v)); econstructor; eauto using types_LF.
(* lam *)
assert (exists v, v \notin L \u used_vars_te_LF M)
  as HF by apply Fresh; destruct HF;
destruct H0 with x G' w; auto; [eapply LF_to_Hyb_ctx_extend2_t; eauto | ];
unfold open_LF in *;
assert (LF_to_Hyb_rel ((x, A) :: Gamma)
         (subst_t_LF (hyp_LF (fte x)) (bte 0) M) B G' w x0) by auto;
apply LF_to_Hyb_rel_subst_t_rev with (M:=hyp_LF (fte x)) (M':=hyp_Hyb (fte x))
                                                         (B:=A)
 in H3.
destruct H3; exists (lam_Hyb A x1);
apply lam_LF_Hyb with (L:=L)(G:=map snd_ G');
[ apply t_lam_LF with (L:=L) | |]; eauto;
intros; subst; unfold open_LF; unfold open_t_Hyb;
replace ((v0, A) :: Gamma) with (subst_in_ctx_LF v0 x ((x,A)::Gamma)).
replace (subst_t_LF (hyp_LF (fte v0)) (bte 0) M) with
   (subst_t_LF (hyp_LF (fte v0)) (fte x)
               (subst_t_LF (hyp_LF (fte x)) (bte 0) M)).
replace G' with (map (subst_in_ctx_Hyb v0 x) G').
replace ([hyp_Hyb (fte v0) // bte 0]x1) with
  ([hyp_Hyb (fte v0) // fte x] ([hyp_Hyb (fte x) // bte 0] x1)).
apply LF_to_Hyb_rel_rename_vars with ((x,A)::Gamma)
      (subst_t_LF (hyp_LF (fte x)) (bte 0) M) G' ([hyp_Hyb (fte x) // bte 0]x1)
      x v0; auto.
rewrite notin_union in H2; destruct H2; rewrite <- subst_t_Hyb_neutral_free;
auto. skip. (* We will find a way, maybe including :
erewrite <- LF_to_Hyb_rel_te_vars with
  (N1:=open_t_LF (hyp_LF (fte x)) M); eauto.
OR we can just say that x is fresher than vars from Gamma and G' -
and prove a (true by design!) lemma that what we want is a subset of what we
have
-- but for this we will need reversed subst_t lemma (R subst M N => R M N)
*)
skip. (* separate lemma *)
rewrite <- subst_t_neutral_free_LF; eauto.
simpl; case_if. skip. (* separate lemma *)
skip. (* Later *)
(* appl *)
destruct IHtypes_LF1 with G' w; auto;
destruct IHtypes_LF2 with G' w; auto;
exists (appl_Hyb x x0); econstructor; eauto; econstructor; eauto.
(* box *)
assert (exists (w: var), w \notin \{}) by apply Fresh; destruct H1.
destruct IHtypes_LF with (G' & (w, Gamma)) x; auto.
rew_map; auto.
apply LF_to_Hyb_ctx_extend2_w; eauto. skip. (* permut *)
exists (box_Hyb x0); econstructor; eauto.
econstructor; eauto.
intros; unfold open_w_Hyb.
replace ((w, Gamma) :: G') with (G' & (w, Gamma)) by skip. (* such rewrite
will require additional lemma *)
replace (G' & (w, Gamma)) with (map (subst_w_in_ctx_Hyb w0 x) (G' & (w, Gamma))).
replace ({{fwo w0 // bwo 0}}x0) with ({{fwo w0//fwo x}}{{fwo x // bwo 0}}x0).
apply LF_to_Hyb_rel_rename_worlds with (G' & (w, Gamma)) ({{fwo x // bwo 0}} x0)
                                       x x w0; eauto.
skip. (* really, x0 is of the form {{fwo x//bwo 0}} x1, but how can we know it
for cerain; maybe we can add lc_w to assumptions (or just conclude it from
typing) and then say that it's closed. so whatevs *)
case_if; auto.
rewrite subst_w_Hyb_neutral_free; auto. skip. (* again, just x notin any
known worlds from G' and (w, Gamma) + it's a subset *)
skip. (* x is free in this, separate lemma *)
(* In general, this was the same story as with lambda -
and with similar lemmas *)
(* unbox *)
destruct IHtypes_LF with G' w; auto.
exists (unbox_fetch_Hyb (fwo w) x); econstructor; eauto; constructor; auto.
(* unbox-fetch *)
assert (exists (G0: bg_Hyb), G = map snd_ G0) by skip. destruct H2 as (G0).
assert (exists w',
          PPermut_Hyb (G0 & (w', Gamma)) G'0) by skip. (* from H0 *)
destruct H3 as (w').
destruct IHtypes_LF with (G0 & (w, Gamma')) w'; auto.
rew_map; simpl; subst; auto.
subst. skip.
exists (unbox_fetch_Hyb (fwo w') x).
replace G'0 with ((w', Gamma) :: G0) by skip. (* lemma mentioned earlier *)
apply unbox_fetch_LF_Hyb with (G:=G); eauto. skip (* from ok + rel on ctxts *).
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto. PPermut_LF_simpl.
skip. (* permuts *)
replace ((w, Gamma')::G0) with (G0 & (w, Gamma')) by skip. auto.
(* here *)
destruct IHtypes_LF with G' w; auto.
exists (get_here_Hyb (fwo w) x); econstructor; eauto; constructor; auto.
(* get-here *)
assert (exists (G0: bg_Hyb), G = map snd_ G0) by skip. destruct H2 as (G0).
assert (exists w',
          PPermut_Hyb (G0 & (w', Gamma)) G'0) by skip. (* from H0 *)
destruct H3 as (w').
destruct IHtypes_LF with (G0 & (w, Gamma')) w'; auto.
rew_map; simpl; subst; auto.
subst. skip.
exists (get_here_Hyb (fwo w') x).
replace G'0 with ((w', Gamma) :: G0) by skip. (* lemma mentioned earlier *)
apply get_here_LF_Hyb with (G:=G); eauto. skip (* from ok + rel on ctxts *).
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto. PPermut_LF_simpl.
skip. (* permuts *)
replace ((w, Gamma')::G0) with (G0 & (w, Gamma')) by skip. auto.
(* letdia *)
assert (exists x, x \notin L) by apply Fresh; destruct H2.
destruct H0 with (((x,A)::nil) :: map snd_ G') x ((x, (x,A)::nil)::G') w; auto.
skip.
assert ( LF_to_Hyb_rel Gamma (open_LF N (hyp_LF (fte x))) B
         ((x, (x, A) :: nil) :: G') w x0) by auto.
skip. (*combination of lambda and box *)
(* letdia-get *)
skip. (* combin. of lambda, box and unbox *)
Qed.

Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
