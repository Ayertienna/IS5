Add LoadPath "..".
Add LoadPath "../Labeled/Lists".
Add LoadPath "../Hybrid".

Require Import Shared.
Require Import Labeled.
Require Import Hybrid.
Require Import Arith.

Open Scope is5_scope.
Open Scope permut_scope.
Open Scope labeled_is5_scope.
Open Scope hybrid_is5_scope.

(* Context conversion *)

Fixpoint annotate_worlds_Hyb (w: var) (L: ctx_LF) : ctx_L :=
match L with
  | nil => nil
  | (x, T) :: L' => (w, (x, T)) :: annotate_worlds_Hyb w L'
end.

Definition Hyb_to_L_ctx (G: bg_Hyb) (Ctx: ctx_Hyb) :
  (list var) * ctx_L * var :=
  let Omega := map fst_ (Ctx :: G) in
  let Delta := flat_map (fun x => annotate_worlds_Hyb (fst_ x) (snd_ x))
    (Ctx :: G) in
  (Omega, Delta, fst Ctx).

(* FIXME: Move this to Hybrid/Hyb_OkLib *)
Lemma ok_Hyb_not_Mem_fst:
forall (G: bg_Hyb) U w,
  ok_Hyb G U -> Mem w U ->
  ~ Mem w (map fst_ G) .
induction G; intros; simpl in *.
rewrite Mem_nil_eq; auto.
destruct a; rew_map; simpl; rewrite Mem_cons_eq; intro; destruct H1; subst.
inversion H; subst; auto; inversion H; subst. apply IHG in H0;
[ contradiction | ]; inversion H; subst; apply ok_Hyb_used_weakening in H7;
auto.
Qed.

(* FIXME: Move this to Hybrid/Hyb_PPermutLib *)
Lemma PPermut_Hyb_map_fst:
forall G G',
  G ~=~ G' ->
  map fst_ G *=* map fst_ G'.
induction G; intros.
apply PPermut_Hyb_nil_impl in H; subst; auto.
assert (a::G ~=~ G') by auto;
destruct a; apply PPermut_Hyb_split_head in H;
destruct H as (l', (hd, (tl, (Ha, Hb)))); subst;
rew_map; simpl; permut_simpl;
replace (map fst_ hd ++ map fst_ tl) with (map fst_ (hd++tl))
  by (rew_map; auto);
apply IHG.
apply PPermut_Hyb_last_rev with (w:=v) (Gamma:=l) (Gamma':=l);
auto; transitivity ((v,l)::G); [ | rewrite H0]; PPermut_Hyb_simpl.
Qed.

Lemma annotate_worlds_Hyb_app:
forall l1 l2 x,
  annotate_worlds_Hyb x (l1++l2) =
  annotate_worlds_Hyb x l1 ++ annotate_worlds_Hyb x l2.
induction l1; intros; rew_app; simpl; auto; destruct a; simpl;
rewrite IHl1; rew_app; auto.
Qed.

Lemma permut_annotate_worlds_Hyb:
forall l l' x,
  l *=* l' -> annotate_worlds_Hyb x l *=* annotate_worlds_Hyb x l'.
induction l; intros.
apply permut_nil_eq in H; subst; auto.
assert (a::l *=* l') by auto;
apply permut_split_head in H; destruct H as (hd, (tl, H)); subst;
destruct a; simpl; repeat rewrite annotate_worlds_Hyb_app; simpl;
permut_simpl; replace (annotate_worlds_Hyb x hd ++ annotate_worlds_Hyb x tl)
with (annotate_worlds_Hyb x (hd++tl)) by (apply annotate_worlds_Hyb_app; auto).
apply IHl;
apply permut_cons_inv with (a:=(v,t)); rewrite H0; permut_simpl.
Qed.

Lemma PPermut_Hyb_flat_map_annotate_worlds_Hyb:
forall G G',
  G ~=~ G' ->
  flat_map (fun x => annotate_worlds_Hyb (fst_ x) (snd_ x)) G *=*
  flat_map (fun x => annotate_worlds_Hyb (fst_ x) (snd_ x)) G'.
induction G; intros.
remember (fun x : var * list (var * ty) =>
            annotate_worlds_Hyb (fst_ x) (snd_ x))
  as g;
apply PPermut_Hyb_nil_impl in H; subst; auto.
assert (a::G ~=~ G') by auto;
destruct a; apply PPermut_Hyb_split_head in H;
destruct H as (l', (hd, (tl, (Ha, Hb)))); subst;
rew_flat_map; simpl;
assert (l *=* l') by auto;
apply permut_annotate_worlds_Hyb with (x:=v) in Ha;
rewrite Ha; permut_simpl;
rewrite IHG with (G':=hd++tl); rew_flat_map; auto;
apply PPermut_Hyb_last_rev with (w:=v) (Gamma:=l) (Gamma':=l);
auto; transitivity ((v,l)::G); [ | rewrite H0]; PPermut_Hyb_simpl.
Qed.

Lemma ok_Hyb_to_L_ctx_ok_Omega_L:
forall G w Gamma Omega,
  ok_Hyb ((w, Gamma)::G) nil ->
  Omega *=* fst_ (fst_ (Hyb_to_L_ctx G (w, Gamma))) ->
  ok_Omega_L Omega.
induction G; intros; inversion H; subst;
[simpl in *; eauto | destruct a];
rew_map in *; simpl in *.
apply ok_Omega_L_permut with (O1:=w::nil);
  [symmetry | constructor]; auto; constructor.
rew_map in *; simpl in *.
inversion H6; subst;
assert (v::w::map fst_ G *=* Omega) by (rewrite H0; permut_simpl).
apply permut_split_head in H1; destruct H1 as (hd, (tl, H1)); subst.
apply ok_Omega_L_permut with (O1:=v::hd++tl); [permut_simpl | constructor].
apply ok_Hyb_not_Mem_fst with (w:=v) in H8; [ | apply Mem_here].
intro. apply Mem_permut with (l':=w::map fst_ G) in H1.
rewrite Mem_cons_eq in H1; destruct H1;
[ subst; elim H7; apply Mem_here | contradiction].
apply permut_cons_inv with (a:=v);
transitivity (hd & v ++ tl); [ | rewrite H0]; permut_simpl.
  apply IHG with (w:=w) (Gamma:=Gamma).
  inversion H6; subst; constructor; auto.
  apply ok_Hyb_used_weakening in H10; auto.
  apply permut_cons_inv with (a:=v);
    transitivity (hd & v ++ tl); [ | rewrite H0]; permut_simpl.
Qed.

Lemma ok_Hyb_to_L_ctx_ok_Gamma_L:
forall G Gamma w Delta U,
  ok_Hyb (flat_map snd_ ((w, Gamma)::G)) U ->
  Delta *=* snd_ (fst_ (Hyb_to_L_ctx G (w, Gamma))) ->
  ok_Gamma_L Delta U.
induction G; induction Gamma; intros; simpl in *; rew_app in *.
symmetry in H0; apply permut_nil_eq in H0; subst; constructor.
destruct a; simpl in *; inversion H; subst;
apply ok_Gamma_L_permut with (G1:=(w, (v, t)) :: annotate_worlds_Hyb w Gamma);
[symmetry | constructor]; auto; apply IHGamma with (w:=w); rew_app; auto.
destruct a; simpl in *;
apply ok_Gamma_L_permut with (G1:=annotate_worlds_Hyb v l ++ flat_map
         (fun x : var * list (var * ty) =>
            annotate_worlds_Hyb (fst_ x) (snd_ x))
         G); [symmetry |]; auto;
apply IHG with (w:=v) (Gamma:=l); auto; permut_simpl.
destruct a0; destruct a; simpl in *; inversion H; subst;
apply ok_Gamma_L_permut with
  (G1:=((w, (v, t)) :: annotate_worlds_Hyb w Gamma) ++
       annotate_worlds_Hyb v0 l ++
       flat_map
         (fun x : var * list (var * ty) =>
            annotate_worlds_Hyb (fst_ x) (snd_ x))
         G); [symmetry |]; auto;
rew_app; constructor; auto;
apply IHGamma with (w:=w); auto; permut_simpl.
Qed.

Lemma ok_Hyb_to_L_ctx_ok_L:
forall G w Gamma Omega Delta,
  ok_Bg_Hyb ((w, Gamma)::G) ->
  Omega *=* fst_ (fst_ (Hyb_to_L_ctx G (w, Gamma))) ->
  Delta *=* snd_ (fst_ (Hyb_to_L_ctx G (w, Gamma))) ->
  ok_L Omega Delta.
intros; destruct H; split;
[eapply ok_Hyb_to_L_ctx_ok_Omega_L |
 eapply ok_Hyb_to_L_ctx_ok_Gamma_L]; eauto.
Qed.

Lemma Mem_preserved_world_L:
forall G w Gamma Omega,
  Omega *=* fst_ (fst_ (Hyb_to_L_ctx G (w, Gamma))) ->
  forall w0 Gamma0,
    Mem (w0, Gamma0) ((w, Gamma)::G) ->
    Mem w0 Omega.
induction G; intros; simpl in *.
rewrite Mem_cons_eq in H0; destruct H0;
[ | rewrite Mem_nil_eq in H0; contradiction];
inversion H0; subst; apply Mem_permut with (l:=map fst_ ((w, Gamma)::nil));
[symmetry; auto | rew_map; simpl; apply Mem_here].
destruct a;
eapply Mem_permut with (l:=map fst_ ((w, Gamma) :: (v, l) :: G));
[symmetry; auto | ]; rewrite Mem_cons_eq in H0; destruct H0.
inversion H0; subst; rew_map; simpl; apply Mem_here.
destruct (eq_var_dec w0 v); subst.
rew_map; simpl; repeat rewrite Mem_cons_eq; right; left; auto.
rewrite Mem_cons_eq in H0; destruct H0.
inversion H0; subst; repeat rewrite Mem_cons_eq; right; left; auto.
rew_map; simpl. apply Mem_permut with (l:=v::w::map fst_ G);
[permut_simpl | rewrite Mem_cons_eq; right];
apply IHG with (w:=w) (Gamma:=Gamma) (Gamma0:=Gamma0).
rew_map; simpl; auto.
rewrite Mem_cons_eq; right; auto.
Qed.

Lemma Mem_annotate_worlds_Hyb:
forall Gamma w Delta x a,
  Delta = annotate_worlds_Hyb w Gamma ->
  (Mem (x, a) Gamma <-> Mem (w, (x, a)) Delta).
induction Gamma; intros; simpl in *; subst.
repeat rewrite Mem_nil_eq; tauto.
destruct a; repeat rewrite Mem_cons_eq; split; intros;
destruct H; try inversion H; subst; simpl in *.
left; auto.
right; apply Mem_here.
destruct y; right; apply IHGamma; auto.
left; auto.
right; eapply IHGamma; eauto; apply Mem_here.
right; eapply IHGamma; eauto. rewrite H0; auto.
Qed.

Lemma Mem_preserved_term_L:
forall G w Gamma Delta,
  Delta *=* snd_ (fst_ (Hyb_to_L_ctx G (w, Gamma))) ->
  forall w0 x0 a0 Gamma0,
    Mem (w0, Gamma0) ((w, Gamma)::G) ->
    Mem (x0, a0) Gamma0 ->
    Mem  (w0, (x0, a0)) Delta.
induction G; intros; simpl in *.
rewrite Mem_cons_eq in H0; destruct H0.
inversion H0; subst;
apply Mem_permut with (l:=annotate_worlds_Hyb w Gamma);
[symmetry; rew_app in *; auto | rew_map; simpl];
eapply Mem_annotate_worlds_Hyb; auto.
rewrite Mem_nil_eq in H0; contradiction.
destruct a; simpl in *.
apply Mem_permut with (l:=annotate_worlds_Hyb w Gamma ++
                          annotate_worlds_Hyb v l ++
  flat_map
        (fun x : var * list (var * ty) =>
           annotate_worlds_Hyb (fst_ x) (snd_ x))
        G);
[symmetry; rew_app in *; auto | rew_map; simpl].
repeat rewrite Mem_cons_eq in H0; repeat rewrite Mem_app_or_eq; destruct H0.
inversion H0; subst.
left; eapply Mem_annotate_worlds_Hyb; auto.
destruct H0.
inversion H0; subst; right; left; eapply Mem_annotate_worlds_Hyb; auto.
right; right; apply IHG with (w:=w) (Gamma:=nil) (Gamma0 := Gamma0);
simpl; auto; rewrite Mem_cons_eq; right; auto.
Qed.

(* Term conversion *)
Fixpoint Hyb_to_L_term (M0: te_Hyb) :=
match M0 with
| hyp_Hyb v =>
  hyp_L v
| lam_Hyb A M =>
  lam_L A (Hyb_to_L_term M)
| appl_Hyb M N =>
  appl_L (Hyb_to_L_term M) (Hyb_to_L_term N)
| box_Hyb M =>
  box_L (Hyb_to_L_term M)
| unbox_fetch_Hyb w M =>
  unbox_L (fetch_L w (Hyb_to_L_term M))
| get_here_Hyb w M =>
  get_L w (here_L (Hyb_to_L_term M))
| letdia_get_Hyb w M N =>
  letd_L (get_L w (Hyb_to_L_term M)) (Hyb_to_L_term N)
end.

Lemma Hyb_to_L_term_subst_t:
forall M N x,
  subst_t_L (Hyb_to_L_term M) x (Hyb_to_L_term N) =
  Hyb_to_L_term (subst_t_Hyb M x N).
induction N; intros; simpl in *;
try rewrite IHN || (rewrite IHN1; rewrite IHN2); auto;
case_if; simpl; auto.
Qed.

Lemma Hyb_to_L_term_subst_w:
forall M w w',
  subst_w_L (Hyb_to_L_term M) w w' =
  Hyb_to_L_term (subst_w_Hyb w w' M).
induction M; intros; simpl in *;
try rewrite IHM || (rewrite IHM1; rewrite IHM2); auto;
case_if; simpl; auto.
Qed.

Lemma Hyb_to_L_typing:
forall G w Gamma M A Omega Delta w' M'
  (HT: G |= (w, Gamma) |- M ::: A)
  (H_Omega: Omega *=* fst_ (fst_ (Hyb_to_L_ctx G (w, Gamma))))
  (H_Delta: Delta *=* snd_ (fst_ (Hyb_to_L_ctx G (w, Gamma))))
  (H_w: w' = snd_ (Hyb_to_L_ctx G (w, Gamma)))
  (H_M: M' = Hyb_to_L_term M),
  Omega; Delta |- M' ::: A @ w.
intros;
unfold Hyb_to_L_ctx in *; rew_flat_map in *; rew_map in *;
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
  eapply ok_Hyb_to_L_ctx_ok_L; simpl; eauto.
  eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
  eapply Mem_preserved_term_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
(* lam *)
apply t_lam_L with (L:=L).
  eapply ok_Hyb_to_L_ctx_ok_L; eauto.
  intros. replace (hyp_L (fte x)) with (Hyb_to_L_term (hyp_Hyb (fte x))).
  unfold open_t_L; rewrite Hyb_to_L_term_subst_t. eapply H; eauto.
  simpl; permut_simpl; auto.
  simpl; auto.
(* appl *)
apply t_appl_L with (A:=A).
  eapply ok_Hyb_to_L_ctx_ok_L; eauto.
  eapply IHHT1; eauto.
  eapply IHHT2; eauto.
(* box *)
apply t_box_L with (L:=L).
  apply ok_Hyb_to_L_ctx_ok_L with (G:=G) (w:=w0) (Gamma:=Gamma0); auto;
    assert ((w0, Gamma0) :: G ~=~ G & (w0, Gamma0)) as H1 by PPermut_Hyb_simpl;
    rewrite H1; auto.
  eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
  intros; unfold open_w_L; rewrite Hyb_to_L_term_subst_w.
  apply H with (Gamma:=nil); auto.
  rewrite H_Delta; simpl; rew_app; rew_flat_map; simpl; permut_simpl.
  rew_map; simpl; rewrite H_Omega; permut_simpl.
(* unbox_fetch *)
apply t_unbox_L.
  eapply ok_Hyb_to_L_ctx_ok_L; eauto.
  apply t_fetch_L.
    eapply ok_Hyb_to_L_ctx_ok_L; eauto.
    eapply IHHT; eauto.
    apply Mem_permut with (l:=w0::map fst_ G);
    [ symmetry | apply Mem_here ]; auto.
apply t_unbox_L.
  eapply ok_Hyb_to_L_ctx_ok_L; eauto.
  simpl; rew_map; simpl; rewrite H_Omega; permut_simpl.
  replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
    by (rew_map; simpl; auto);
  apply PPermut_Hyb_map_fst; rewrite <- H; PPermut_Hyb_simpl.
  simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
  apply PPermut_Hyb_flat_map_annotate_worlds_Hyb in H; rew_map in *;
    rewrite <- H; rew_flat_map; simpl; permut_simpl.
  apply t_fetch_L.
    eapply ok_Hyb_to_L_ctx_ok_L; eauto.
    rewrite H_Omega; symmetry; simpl; rew_map; simpl; permut_simpl.
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_Hyb_map_fst; rewrite <- H; PPermut_Hyb_simpl.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
    apply PPermut_Hyb_flat_map_annotate_worlds_Hyb in H; rew_map in *;
      rewrite <- H; rew_flat_map; simpl; permut_simpl.
    eapply IHHT; eauto.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
    apply PPermut_Hyb_flat_map_annotate_worlds_Hyb in H; rew_map in *;
      rewrite <- H; rew_flat_map; simpl; permut_simpl.
    rewrite H_Omega; rew_map; simpl; permut_simpl.
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_Hyb_map_fst; rewrite <- H; PPermut_Hyb_simpl.
    eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
(* get_here *)
apply t_get_L.
  eapply ok_Hyb_to_L_ctx_ok_L; eauto.
  apply t_here_L.
    eapply ok_Hyb_to_L_ctx_ok_L; eauto.
    eapply IHHT; eauto.
    apply Mem_permut with (l:=w0::map fst_ G);
    [ symmetry | apply Mem_here ]; auto.
apply t_get_L.
  eapply ok_Hyb_to_L_ctx_ok_L; eauto.
  simpl; rew_map; simpl; rewrite H_Omega; permut_simpl.
  replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
    by (rew_map; simpl; auto);
  apply PPermut_Hyb_map_fst; rewrite <- H; PPermut_Hyb_simpl.
  simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
  apply PPermut_Hyb_flat_map_annotate_worlds_Hyb in H; rew_map in *;
    rewrite <- H; rew_flat_map; simpl; permut_simpl.
  apply t_here_L.
    eapply ok_Hyb_to_L_ctx_ok_L; eauto.
    rewrite H_Omega; symmetry; simpl; rew_map; simpl; permut_simpl.
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_Hyb_map_fst; rewrite <- H; PPermut_Hyb_simpl.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
    apply PPermut_Hyb_flat_map_annotate_worlds_Hyb in H; rew_map in *;
      rewrite <- H; rew_flat_map; simpl; permut_simpl.
    eapply IHHT; eauto.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl.
    apply PPermut_Hyb_flat_map_annotate_worlds_Hyb in H; rew_map in *;
      rewrite <- H; rew_flat_map; simpl; permut_simpl.
    rewrite H_Omega; rew_map; simpl; permut_simpl.
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_Hyb_map_fst; rewrite <- H; PPermut_Hyb_simpl.
    eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
(* letdia_get *)
apply t_letd_L with (A:=A) (Lt:=L_t) (Lw:=L_w).
  eapply ok_Hyb_to_L_ctx_ok_L; eauto.
  apply t_get_L.
    eapply ok_Hyb_to_L_ctx_ok_L; eauto.
    eapply IHHT; eauto.
    eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
  intros; unfold open_t_Hyb in *; unfold open_w_Hyb in *;
  unfold open_t_L in *; unfold open_w_L in *.
    rewrite Hyb_to_L_term_subst_w.
    replace (hyp_L (fte t)) with (Hyb_to_L_term (hyp_Hyb (fte t))).
    rewrite Hyb_to_L_term_subst_t.
    eapply H; eauto.
    rewrite H_Delta; rew_map; simpl; permut_simpl.
    rewrite H_Omega; rew_map; simpl; permut_simpl.
    simpl; auto.
apply t_letd_L with (A:=A) (Lt:=L_t) (Lw:=L_w).
  eapply ok_Hyb_to_L_ctx_ok_L; eauto.
  rewrite H_Omega; simpl; rew_map; simpl; permut_simpl;
  replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
    by (rew_map; simpl; auto);
  apply PPermut_Hyb_map_fst; rewrite <- H0; PPermut_Hyb_simpl.
  simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl;
  apply PPermut_Hyb_flat_map_annotate_worlds_Hyb in H0; rew_map in *;
  rewrite <- H0; rew_flat_map; simpl; permut_simpl.
  apply t_get_L.
    eapply ok_Hyb_to_L_ctx_ok_L; eauto.
    rewrite H_Omega; simpl; rew_map; simpl; permut_simpl;
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_Hyb_map_fst; rewrite <- H0; PPermut_Hyb_simpl.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl;
    apply PPermut_Hyb_flat_map_annotate_worlds_Hyb in H0; rew_map in *;
    rewrite <- H0; rew_flat_map; simpl; permut_simpl.
    eapply IHHT; eauto.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl;
    apply PPermut_Hyb_flat_map_annotate_worlds_Hyb in H0; rew_map in *;
    rewrite <- H0; rew_flat_map; simpl; permut_simpl.
    rewrite H_Omega; simpl; rew_map; simpl; permut_simpl;
    replace ((w::nil) ++ map fst_ G) with (map fst_ ((w, Gamma)::G))
      by (rew_map; simpl; auto);
    apply PPermut_Hyb_map_fst; rewrite <- H0; PPermut_Hyb_simpl.
    eapply Mem_preserved_world_L with (w:=w0) (Gamma:=Gamma0);
    simpl; eauto; eapply Mem_here.
    intros; unfold open_t_Hyb in *; unfold open_w_Hyb in *;
    unfold open_t_L in *; unfold open_w_L in *.
    rewrite Hyb_to_L_term_subst_w.
    replace (hyp_L (fte t)) with (Hyb_to_L_term (hyp_Hyb (fte t))).
    rewrite Hyb_to_L_term_subst_t.
    eapply H; eauto.
    simpl; rewrite H_Delta; rew_flat_map; simpl; permut_simpl;
    apply PPermut_Hyb_flat_map_annotate_worlds_Hyb in H0; rew_map in *;
    rewrite <- H0; rew_flat_map; simpl; permut_simpl.
    rewrite H_Omega; simpl; rew_map; simpl; permut_simpl.
    replace (map fst_ G & w) with (map fst_ (G & (w, Gamma)))
      by (rew_map; simpl; auto);
    apply PPermut_Hyb_map_fst; rewrite <- H0; PPermut_Hyb_simpl.
    simpl; auto.
Qed.

(*
Lemma lc_w_rewrite_L:
forall M n,
  lc_w_n_Hyb n M -> lc_w_n_L n (Hyb_to_L_term M).
induction M; intros; inversion H; subst; simpl in *;
try destruct v; repeat constructor; eauto.
Qed.

Lemma lc_t_rewrite_L:
forall M n,
  lc_t_n_Hyb n M -> lc_t_n_L n (Hyb_to_L_term M).
induction M; intros; inversion H; subst; simpl in *;
repeat constructor; eauto.
Qed.

(* FIXME: Move these & rename
Lemma lc_t_n_L_subst_w:
forall M w w' n,
  lc_t_n_L n M ->
  lc_t_n_L n (subst_w_L M w w').
induction M; intros; simpl in *; auto;
constructor; inversion H; subst; eauto.
Qed.

Lemma lc_w_n_L_subst_t:
forall M N x n,
  lc_w_n_L n M -> lc_w_L N ->
  lc_w_n_L n (subst_t_L N x M).
induction M; intros; simpl in *; auto; repeat case_if; simpl;
unfold shift_vte in *; unfold shift_vwo in *;
try destruct x; simpl in *; auto;
try (inversion H; econstructor; eauto).
replace n with (0+n) by omega; apply closed_w_addition_L; auto.
replace n with (0+n) by omega; apply closed_w_addition_L; auto.
Qed.

Lemma lc_t_step_preserv:
forall M N w,
  lc_t_L M ->
  step_L (M, w) (N, w) ->
  lc_t_L N.
induction M; intros; inversion H0; subst; auto;
unfold open_t_L in *; unfold open_w_L in *.
constructor; [eapply IHM1 |]; eauto.
apply lc_t_subst_w; auto.
constructor; eapply IHM; eauto.
constructor; eapply IHM; eauto.
inversion H; subst;
apply lc_t_subst_w; auto.
rewrite <- subst_order_irrelevant_bound_L; auto;
apply lc_t_subst_w; auto.
inversion H; subst; constructor; auto; eapply IHM1; eauto.
constructor; eapply IHM; eauto.
constructor; eapply IHM; eauto.
apply lc_t_subst_w; auto.
Qed.

Lemma lc_w_step_preserv:
forall M N w,
  lc_w_L M ->
  step_L (M, w) (N, w) ->
  lc_w_L N.
induction M; intros; inversion H0; subst; auto;
unfold open_t_L in *; unfold open_w_L in *; simpl in *.
eapply lc_w_subst_L.
constructor; [eapply IHM1 |]; eauto.
apply lc_t_subst_w; auto.
constructor; eapply IHM; eauto.
constructor; eapply IHM; eauto.
inversion H; subst; constructor.
apply lc_t_subst_w; auto.
rewrite <- subst_order_irrelevant_bound_L; auto;
apply lc_t_subst_w; auto.
inversion H; subst; constructor; auto; eapply IHM1; eauto.
constructor; eapply IHM; eauto.
constructor; eapply IHM; eauto.
apply lc_t_subst_w; auto.
Qed.
*)


Lemma appl_steps:
forall M M' N w,
  lc_t_L M -> lc_t_L N -> lc_w_L M -> lc_w_L N ->
  steps_L (M, w) (M', w) ->
  steps_L (appl_L M N, w) (appl_L M' N, w).
intros; remember (M, w) as S0; remember (M', w) as S1;
generalize dependent N;
generalize dependent M; generalize dependent M';
generalize dependent w.
induction H3; intros; inversion HeqS1; inversion HeqS0; subst.
constructor; constructor; auto.
apply multi_step_L with (M':=appl_L M' N).
  constructor; auto.
  apply IHsteps_L; auto.
  apply lc_t_step_preserv with (M:=M0) (w:=w0); eauto.
  apply lc_w_step_preserv with (M:=M0) (w:=w0); eauto.

inversion H; subst;
  unfold open_t_L; unfold open_w_L; auto.
  app




Lemma labeled_step:
forall M M' w,
  step_Hyb (M, w) (M', w) ->
  steps_L (Hyb_to_L_term M, w) (Hyb_to_L_term M', w).
induction M; intros;
inversion H; subst; simpl in *;
unfold open_t in *; unfold open_w in *; simpl in *.
(* appl_lam *)
constructor;
rewrite <- subst_t_rewrite_L; constructor;
unfold open_t_L;
repeat rewrite <- subst_w_rewrite_L;
apply lc_t_subst || apply lc_w_subst || simpl;
apply lc_w_rewrite_L ||
apply lc_t_rewrite_L || eauto; auto.
(* appl *)
apply IHM1 in HT.
inversion HT; subst.
  constructor; constructor; auto;
  apply lc_w_rewrite_L ||
  apply lc_t_rewrite_L; eauto.
  apply multi_step_L with (M':=appl_L M' (Hyb_to_L_term M2)).
    constructor; auto;
    apply lc_w_rewrite_L ||
    apply lc_t_rewrite_L; eauto.

inversion H3; subst;
[inversion HT | ].
constructor. constructor.
inversion H.
eapply IHM1 in HT0; eauto.

constructor;
try (apply lc_t_subst);
try (apply lc_w_subst);
apply lc_w_rewrite_L ||
apply lc_t_rewrite_L || eauto; eauto.
inversion H3; subst.
  inversion HT. apply single_step_Hyb in HT0.
eapply IHM1 in HT0; eauto.
eapply HT in IHM1. eauto; inversion HT; subst; auto.

*)

Close Scope labeled_is5_scope.
Close Scope hybrid_is5_scope.
