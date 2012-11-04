(* LL <-> LF (labeled <-> hybrid) *)
Require Import Labeled.
Require Import LabelFree.
Require Import LibVar.
Require Import LibLogic.
Require Import LibList.
Require Import LibListSorted.
Require Import OkLib.
Require Import LLOkLib.

Open Scope labeled_is5_scope.
Open Scope label_free_is5_scope.
Open Scope is5_scope.
Open Scope permut_scope.

Section LF_to_L.

Fixpoint annotate_worlds (w: var) (L: list (var * ty)) : Context_L :=
match L with
  | nil => nil
  | (x, T) :: L' => (w, (x, T)) :: annotate_worlds w L'
end.

Definition labeled_context (G: Background_LF) (Ctx: Context_LF) :
  (list var) * Context_L * var :=
  let Omega := map fst_ (Ctx :: G) in
  let Delta := flat_map (fun x => annotate_worlds (fst_ x) (snd_ x))
    (Ctx :: G) in
  (Omega, Delta, fst Ctx).

Fixpoint labeled_term (M0: te_LF) :=
match M0 with
| hyp_LF v =>
  hyp_L v
| lam_LF A M =>
  lam_L A (labeled_term M)
| appl_LF M N =>
  appl_L (labeled_term M) (labeled_term N)
| box_LF M =>
  box_L (labeled_term M)
| unbox_fetch_LF w M =>
  unbox_L (fetch_L w (labeled_term M))
| get_here_LF w M =>
  get_L w (here_L (labeled_term M))
| letdia_get_LF w M N =>
  letd_L (get_L w (labeled_term M)) (labeled_term N)
end.

(* FIXME: move this :) *)
Lemma ok_LF_not_Mem_fst:
forall (G: Background_LF) U w,
  ok_LF G U -> Mem w U ->
  ~ Mem w (map fst_ G) .
induction G; intros; simpl in *.
rewrite Mem_nil_eq; auto.
destruct a; rew_map; simpl; rewrite Mem_cons_eq; intro; destruct H1; subst.
inversion H; subst; auto; inversion H; subst. apply IHG in H0;
[ contradiction | ]; inversion H; subst; apply ok_LF_used_weakening in H7; auto.
Qed.

Lemma PPermut_map_fst:
forall G G',
  G ~=~ G' ->
  map fst_ G *=* map fst_ G'.
Admitted.

Lemma PPermut_flat_map_annotate_worlds:
forall G G',
  G ~=~ G' ->
  flat_map (fun x => annotate_worlds (fst_ x) (snd_ x)) G *=*
  flat_map (fun x => annotate_worlds (fst_ x) (snd_ x)) G'.
Admitted.

(* until here *)

Lemma ok_LF_impl_ok_Omega:
forall G w Gamma Omega,
  ok_LF ((w, Gamma)::G) nil ->
  Omega *=* fst_ (fst_ (labeled_context G (w, Gamma))) ->
  ok_Omega Omega.
(*
induction G; intros; inversion H; subst;
[simpl in *; eauto | destruct a].
unfold labeled_context; rew_map; simpl; repeat split.
rewrite Mem_cons_eq; intro; destruct H0; subst; inversion H6; subst;
[elim H4; apply Mem_here | ].
simpl. apply ok_LF_not_Mem_fst with (w:=w) in H8;
[contradiction | repeat rewrite Mem_cons_eq]; right; left; auto.
inversion H6; subst;
apply ok_LF_not_Mem_fst with (U:=v::w::nil); auto; apply Mem_here.
assert (ok_Omega (map fst_ ((w, Gamma) :: G))).
  apply IHG with (w:=w) (Gamma:=Gamma).
  inversion H6; subst; constructor; auto.
  apply ok_LF_used_weakening in H7; auto.
  rew_map; simpl; symmetry; rew_map; simpl; auto.
  rew_map in *; simpl in *; destruct H0; auto.
*)
Admitted.

Lemma ok_LF_impl_ok_Gamma:
forall G w Gamma Delta U,
  ok_LF (flat_map snd_ ((w, Gamma)::G)) U ->
  Delta *=* snd_ (fst_ (labeled_context G (w, Gamma))) ->
  ok_Gamma Delta U.
Admitted.

Lemma ok_Bg_impl_ok_L:
forall G w Gamma Omega Delta,
  ok_Bg ((w, Gamma)::G) ->
  Omega *=* fst_ (fst_ (labeled_context G (w, Gamma))) ->
  Delta *=* snd_ (fst_ (labeled_context G (w, Gamma))) ->
  ok_L Omega Delta.
intros; destruct H; split;
[eapply ok_LF_impl_ok_Omega |
 eapply ok_LF_impl_ok_Gamma]; eauto.
Qed.

Lemma Mem_preserved_world_L:
forall G w Gamma Omega Delta,
  Omega *=* fst_ (fst_ (labeled_context G (w, Gamma))) ->
  Delta *=* snd_ (fst_ (labeled_context G (w, Gamma))) ->
  forall w0 Gamma0,
    Mem (w0, Gamma0) ((w, Gamma)::G) ->
    Mem w0 Omega.
Admitted.

Lemma Mem_preserved_term_L:
forall G w Gamma Omega Delta,
  Omega *=* fst_ (fst_ (labeled_context G (w, Gamma))) ->
  Delta *=* snd_ (fst_ (labeled_context G (w, Gamma))) ->
  forall w0 x0 a0 Gamma0,
    Mem (w0, Gamma0) ((w, Gamma)::G) ->
    Mem (x0, a0) Gamma0 ->
    Mem  (w0, (x0, a0)) Delta.
Admitted.

Lemma subst_t_rewrite_L:
forall M N x,
  subst_t_L (labeled_term M) x (labeled_term N) =
  labeled_term (subst_t M x N).
Admitted.

Lemma subst_w_rewrite_L:
forall M w w',
  subst_w_L (labeled_term M) w w' =
  labeled_term (subst_w w w' M).
Admitted.

Lemma labeled_typing:
forall G w Gamma M A Omega Delta w' M'
  (HT: G |= (w, Gamma) |- M ::: A)
  (H_Omega: Omega *=* fst_ (fst_ (labeled_context G (w, Gamma))))
  (H_Delta: Delta *=* snd_ (fst_ (labeled_context G (w, Gamma))))
  (H_w: w' = snd_ (labeled_context G (w, Gamma)))
  (H_M: M' = labeled_term M),
  Omega; Delta |- M' ::: A @ w.
intros;
unfold labeled_context in *; rew_flat_map in *; rew_map in *;
simpl in *; subst;
generalize dependent Omega;
generalize dependent Delta;
remember (w, Gamma) as Ctx;
generalize dependent w;
generalize dependent Gamma.
induction HT;
intros; inversion HeqCtx; subst; simpl in *.
(* hyp *)
apply t_hyp_L.
  eapply ok_Bg_impl_ok_L; simpl; eauto.
  eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
  eapply Mem_preserved_term_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
(* lam *)
apply t_lam_L with (L:=L).
  eapply ok_Bg_impl_ok_L; eauto.
  intros. replace (hyp_L (fte x)) with (labeled_term (hyp_LF (fte x))).
  unfold open_t_L; rewrite subst_t_rewrite_L. eapply H; eauto.
  simpl; permut_simpl; auto.
  simpl; auto.
(* appl *)
apply t_appl_L with (A:=A).
  eapply ok_Bg_impl_ok_L; eauto.
  eapply IHHT1; eauto.
  eapply IHHT2; eauto.
(* box *)
apply t_box_L with (L:=L).
  apply ok_Bg_impl_ok_L with (G:=G) (w:=w0) (Gamma:=Gamma0); auto;
    assert ((w0, Gamma0) :: G ~=~ G & (w0, Gamma0)) as H1 by PPermut_simpl;
    rewrite H1; auto.
  eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
  intros; unfold open_w_L; rewrite subst_w_rewrite_L.
  apply H with (Gamma:=nil); auto.
  rewrite H_Delta; simpl; rew_app; rew_flat_map; simpl; permut_simpl.
  rew_map; simpl; rewrite H_Omega; permut_simpl.
(* unbox_fetch *)
apply t_unbox_L.
  eapply ok_Bg_impl_ok_L; eauto.
  apply t_fetch_L.
    eapply ok_Bg_impl_ok_L; eauto.
    eapply IHHT; eauto.
    apply Mem_permut with (l:=w0::map fst_ G);
    [ symmetry | apply Mem_here ]; auto.
apply t_unbox_L.
  eapply ok_Bg_impl_ok_L; eauto.
  simpl; rew_map; simpl; rewrite H_Omega; permut_simpl.
  replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
    by (rew_map; simpl; auto);
  apply PPermut_map_fst; rewrite <- H; PPermut_simpl.
  simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
  apply PPermut_flat_map_annotate_worlds in H; rew_map in *;
    rewrite <- H; rew_flat_map; simpl; permut_simpl.
  apply t_fetch_L.
    eapply ok_Bg_impl_ok_L; eauto.
    rewrite H_Omega; symmetry; simpl; rew_map; simpl; permut_simpl.
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_map_fst; rewrite <- H; PPermut_simpl.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
    apply PPermut_flat_map_annotate_worlds in H; rew_map in *;
      rewrite <- H; rew_flat_map; simpl; permut_simpl.
    eapply IHHT; eauto.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
    apply PPermut_flat_map_annotate_worlds in H; rew_map in *;
      rewrite <- H; rew_flat_map; simpl; permut_simpl.
    rewrite H_Omega; rew_map; simpl; permut_simpl.
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_map_fst; rewrite <- H; PPermut_simpl.
    eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
(* get_here *)
apply t_get_L.
  eapply ok_Bg_impl_ok_L; eauto.
  apply t_here_L.
    eapply ok_Bg_impl_ok_L; eauto.
    eapply IHHT; eauto.
    apply Mem_permut with (l:=w0::map fst_ G);
    [ symmetry | apply Mem_here ]; auto.
apply t_get_L.
  eapply ok_Bg_impl_ok_L; eauto.
  simpl; rew_map; simpl; rewrite H_Omega; permut_simpl.
  replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
    by (rew_map; simpl; auto);
  apply PPermut_map_fst; rewrite <- H; PPermut_simpl.
  simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
  apply PPermut_flat_map_annotate_worlds in H; rew_map in *;
    rewrite <- H; rew_flat_map; simpl; permut_simpl.
  apply t_here_L.
    eapply ok_Bg_impl_ok_L; eauto.
    rewrite H_Omega; symmetry; simpl; rew_map; simpl; permut_simpl.
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_map_fst; rewrite <- H; PPermut_simpl.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
    apply PPermut_flat_map_annotate_worlds in H; rew_map in *;
      rewrite <- H; rew_flat_map; simpl; permut_simpl.
    eapply IHHT; eauto.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
    apply PPermut_flat_map_annotate_worlds in H; rew_map in *;
      rewrite <- H; rew_flat_map; simpl; permut_simpl.
    rewrite H_Omega; rew_map; simpl; permut_simpl.
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_map_fst; rewrite <- H; PPermut_simpl.
    eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
(* letdia_get *)
apply t_letd_L with (A:=A) (Lt:=L_t) (Lw:=L_w).
  eapply ok_Bg_impl_ok_L; eauto.
  apply t_get_L.
    eapply ok_Bg_impl_ok_L; eauto.
    eapply IHHT; eauto.
    eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
  intros; unfold open_t in *; unfold open_w in *;
  unfold open_t_L in *; unfold open_w_L in *.
    rewrite subst_w_rewrite_L.
    replace (hyp_L (fte t)) with (labeled_term (hyp_LF (fte t))).
    rewrite subst_t_rewrite_L.
    eapply H; eauto.
    rewrite H_Delta; rew_map; simpl; permut_simpl.
    rewrite H_Omega; rew_map; simpl; permut_simpl.
    simpl; auto.
apply t_letd_L with (A:=A) (Lt:=L_t) (Lw:=L_w).
  eapply ok_Bg_impl_ok_L; eauto.
  rewrite H_Omega; simpl; rew_map; simpl; permut_simpl;
  replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
    by (rew_map; simpl; auto);
  apply PPermut_map_fst; rewrite <- H0; PPermut_simpl.
  simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl;
  apply PPermut_flat_map_annotate_worlds in H0; rew_map in *;
  rewrite <- H0; rew_flat_map; simpl; permut_simpl.
  apply t_get_L.
    eapply ok_Bg_impl_ok_L; eauto.
    rewrite H_Omega; simpl; rew_map; simpl; permut_simpl;
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_map_fst; rewrite <- H0; PPermut_simpl.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl;
    apply PPermut_flat_map_annotate_worlds in H0; rew_map in *;
    rewrite <- H0; rew_flat_map; simpl; permut_simpl.
    eapply IHHT; eauto.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl;
    apply PPermut_flat_map_annotate_worlds in H0; rew_map in *;
    rewrite <- H0; rew_flat_map; simpl; permut_simpl.
    rewrite H_Omega; simpl; rew_map; simpl; permut_simpl;
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_map_fst; rewrite <- H0; PPermut_simpl.
    eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
    intros; unfold open_t in *; unfold open_w in *;
    unfold open_t_L in *; unfold open_w_L in *.
    rewrite subst_w_rewrite_L.
    replace (hyp_L (fte t)) with (labeled_term (hyp_LF (fte t))).
    rewrite subst_t_rewrite_L.
    eapply H; eauto.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl;
    apply PPermut_flat_map_annotate_worlds in H0; rew_map in *;
    rewrite <- H0; rew_flat_map; simpl; permut_simpl.
    rewrite H_Omega; simpl; rew_map; simpl; permut_simpl.
    replace (map fst_ G & w) with (map fst_ (G & (w, Gamma)))
      by (rew_map; simpl; auto);
    apply PPermut_map_fst; rewrite <- H0; PPermut_simpl.
    simpl; auto.
Qed.

End LF_to_L.

Section L_to_LF.

(* label-free from labeled *)
Fixpoint filter_w (L: Context_L) (e: var) :=
match L with
| nil => nil
| (w, (x, t)) :: L' =>
  if (eq_var_dec e w) then
    (x, t) :: filter_w L' e
  else filter_w L' e
end.

Fixpoint label_free_context (Omega: list var) Gamma w :
  Background_LF * Context_LF :=
match Omega with
| nil => (nil, (w, nil))
| w0 :: Omega' =>
  let (G, Delta) := label_free_context Omega' Gamma w in
  let curr := filter_w Gamma w in
  If w = w0 then
  (* we assume that Delta did not result in anything interesting
     -- we can do this if ok_L Omega Gamma
     because every world should be only once in Omega, so w should be there once
     as well - and this means that Delta = (w, nil) *)
    (G, (w, curr))
  else
    ((w, curr) :: G, Delta)
end.

Fixpoint label_free_term (M0: te_L) (w: vwo) :=
match M0 with
| hyp_L v =>
  hyp_LF v
| lam_L A M =>
  lam_LF A (label_free_term M w)
| appl_L M N =>
  appl_LF (label_free_term M w)  (label_free_term N w)
| box_L M =>
  box_LF (label_free_term M w)
| unbox_L M =>
  unbox_fetch_LF w (label_free_term M w)
| here_L M =>
  get_here_LF w (label_free_term M w)
| letd_L M N =>
  letdia_get_LF w (label_free_term M w) (label_free_term N w)
(* ? *)
| get_L w0 M =>
  letdia_get_LF w0 (label_free_term M w) (get_here_LF w0 (hyp_LF (bte 0)))
(* note: do we need to ensure for fetch that w0 used down there is fresh? *)
| fetch_L w0 M =>
  box_LF (unbox_fetch_LF w0 (label_free_term M w0))
end.

Lemma ok_L_impl_ok_Bg:
forall Omega Gamma w G Delta,
  ok_L Omega Gamma ->
  (G, (w, Delta)) = label_free_context Omega Gamma w ->
  ok_Bg ((w, Delta)::G).
Admitted.

Lemma label_free_typing:
forall Omega Gamma M A w G Delta M' A'
  (HT: Omega; Gamma |- M ::: A @ w)
  (H_G: label_free_context Omega Gamma w = (G, (w, Delta)))
  (H_M: M' = label_free_term M (fwo w)),
  G |= (w, Delta) |- M' ::: A'.
Admitted.