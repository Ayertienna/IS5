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

(* FIXME: Prove & Move *)

Lemma lc_w_step_Hyb_preserv:
forall M M' w,
  lc_w_Hyb M ->
  step_Hyb (M, w) (M', w) ->
  lc_w_Hyb M'.
Admitted.

Lemma lc_t_step_Hyb_preserv:
forall M M' w,
  lc_t_Hyb M ->
  step_Hyb (M, w) (M', w) ->
  lc_t_Hyb M'.
Admitted.

Lemma lc_w_steps_Hyb_preserv:
forall M M' w,
  lc_w_Hyb M ->
  steps_Hyb (M, w) (M', w) ->
  lc_w_Hyb M'.
Admitted.

Lemma lc_t_steps_Hyb_preserv:
forall M M' w,
  lc_t_Hyb M ->
  steps_Hyb (M, w) (M', w) ->
  lc_t_Hyb M'.
Admitted.

(* Lemmas regarding multi-step reductions *)

Lemma steps_Hyb_unbox:
forall M w' w M',
 lc_w_Hyb M -> lc_t_Hyb M ->
 steps_Hyb (M, w') (M', w') ->
 steps_Hyb
   (unbox_fetch_Hyb w' M, w)
   (unbox_fetch_Hyb w' M', w).
intros; remember (M, w') as M0; remember (M', w') as M1;
generalize dependent M;
generalize dependent M';
generalize dependent w';
generalize dependent w;
induction H1; intros; inversion HeqM1; inversion HeqM0; subst;
[constructor; constructor; auto | ];
apply multi_step_Hyb with (M':=unbox_fetch_Hyb w' M');
[ constructor | eapply IHsteps_Hyb ]; eauto;
[eapply lc_w_step_Hyb_preserv | eapply lc_t_step_Hyb_preserv]; eauto.
Qed.

Lemma steps_Hyb_get:
forall M M'' w0 w1 w M' w'0,
  (w0 = fwo w'0 \/ w0 = bwo 0) ->
  lc_w_Hyb M' -> lc_t_Hyb M' ->
  lc_w_n_Hyb 1 M -> lc_t_n_Hyb 1 M ->
  steps_Hyb (M', w) (M'', w) ->
  steps_Hyb
    (letdia_get_Hyb w M' (get_here_Hyb w0 M), w1)
    (letdia_get_Hyb w M'' (get_here_Hyb w0 M), w1).
intros.
remember (M', w) as M0; remember (M'', w) as M1;
generalize dependent M;
generalize dependent M';
generalize dependent M''.
generalize dependent w;
generalize dependent w0;
generalize dependent w'0;
generalize dependent w1.
induction H4; intros; inversion HeqM1; inversion HeqM0; subst;
[constructor; constructor; auto |].
inversion H0; subst; constructor; try omega; auto.
constructor; auto.
apply multi_step_Hyb with (M':= letdia_get_Hyb w2 M' (get_here_Hyb w0 M0));
[ constructor | eapply IHsteps_Hyb ]; eauto.
inversion H0; subst; constructor; try omega; auto.
constructor; auto.
eapply lc_w_step_Hyb_preserv in H1; eauto.
eapply lc_t_step_Hyb_preserv in H2; eauto.
Qed.

Lemma steps_Hyb_appl:
forall M N w M',
 steps_Hyb (M, w) (N, w) ->
 steps_Hyb
   (appl_Hyb M M', w)
   (appl_Hyb N M', w).
Admitted.

Lemma steps_Hyb_here:
forall M w' w M',
 steps_Hyb (M, w') (M', w') ->
 steps_Hyb
   (get_here_Hyb w' M, w)
   (get_here_Hyb w' M', w).
Admitted.

Lemma steps_Hyb_letdia:
forall M w' w M' N,
 steps_Hyb (M, w') (M', w') ->
 steps_Hyb
   (letdia_get_Hyb w' M N, w)
   (letdia_get_Hyb w' M' N, w).
Admitted.

Lemma steps_Hyb_letdia_here:
forall M N w0 w1 w M',
 steps_Hyb (M, w0) (N, w0) ->
 steps_Hyb
   (letdia_get_Hyb w (get_here_Hyb w0 M) M', w1)
   ((M' ^w^ w0) ^t^ N, w1).
Admitted.

(* Context conversion *)

Fixpoint gather_keys_L (k: var) (l: ctx_L) :=
match l with
| nil => nil
| (k', v) :: l' =>
  if (eq_var_dec k k')
  then v :: (gather_keys_L k l')
  else gather_keys_L k l'
end.

Fixpoint bucket_sort_L
         (keys: worlds_L)
         (l: ctx_L) :=
match keys with
| nil => nil
| k :: keys' =>
  (k, gather_keys_L k l) :: bucket_sort_L keys' l
end.

Fixpoint split_at_Hyb (l: bg_Hyb) (k: var) :=
match l with
| nil => (nil, None)
| (k', l) :: l' =>
  let res := split_at_Hyb l' k in
  if (eq_var_dec k k')
  then (l', Some (k', l))
  else ((k',l) :: fst res, snd res)
end.

Definition L_to_Hyb_ctx
         (Omega_L: worlds_L)
         (Gamma_L: ctx_L)
         (w_L: var) :
         (bg_Hyb * option ctx_Hyb) :=
  let G := bucket_sort_L Omega_L Gamma_L in
  split_at_Hyb G w_L.

Lemma L_to_Hyb_ctx_Mem_Some:
forall Omega Gamma w,
  Mem w Omega ->
  exists Delta,
  snd (L_to_Hyb_ctx Omega Gamma w) = Some (w, Delta).
unfold L_to_Hyb_ctx; intros;
remember (bucket_sort_L Omega Gamma) as l;
generalize dependent Omega; generalize dependent Gamma;
generalize dependent w; induction l; intros.
destruct Omega; simpl in *;
[rewrite Mem_nil_eq in H; contradiction | inversion Heql].
destruct a; simpl; case_if; simpl; [eexists; auto | ];
destruct Omega; simpl in *; inversion Heql; subst;
apply IHl with (Gamma0:=Gamma) (Omega0:=Omega) (w:=w); auto;
rewrite Mem_cons_eq in H; destruct H; contradiction || auto.
Qed.

Lemma Mem_gather_keys_L:
forall Gamma w v A,
  Mem (w, (v, A)) Gamma ->
  Mem (v,A) (gather_keys_L w Gamma).
induction Gamma; intros;
[rewrite Mem_nil_eq in H; contradiction | ];
destruct a; destruct p; rewrite Mem_cons_eq in H; destruct H; simpl;
[inversion H; subst; case_if; apply Mem_here |
 case_if; [rewrite Mem_cons_eq; right | ]; apply IHGamma; auto].
Qed.

Lemma Mem_L_to_Hyb_ctx:
forall Omega Gamma w v A G0 G Delta,
  bucket_sort_L Omega Gamma = G0 ->
  split_at_Hyb G0 w = (G, Some (w, Delta)) ->
  Mem (w, (v,A)) Gamma ->
  Mem (v, A) Delta.
induction Omega; intros; inversion Gamma; subst; simpl in *;
try case_if; inversion H0; subst;
try (apply Mem_gather_keys_L; auto).
apply IHOmega with (G0:=bucket_sort_L Omega Gamma)
                   (G:=fst (split_at_Hyb (bucket_sort_L Omega Gamma) w))
                   (Gamma:=Gamma) (w:=w);
auto; rewrite <- H4; rewrite <- surjective_pairing; auto.
apply IHOmega with (G0:=bucket_sort_L Omega Gamma)
                   (G:=fst (split_at_Hyb (bucket_sort_L Omega Gamma) w))
                   (Gamma:=Gamma) (w:=w);
auto; rewrite <- H6; rewrite <- surjective_pairing; auto.
Qed.

Lemma split_at_Hyb_not_Mem:
forall G w,
  (forall Delta , ~ (Mem (w, Delta) G)) ->
  split_at_Hyb G w = (G, None).
induction G; intros; try destruct a; simpl; auto; case_if.
specialize H with l; elim H; apply Mem_here.
specialize IHG with w;
assert ((fst (split_at_Hyb G w), snd (split_at_Hyb G w)) = (G, None)).
  rewrite <- surjective_pairing; rewrite IHG; auto;
  intros; specialize H with Delta; rewrite Mem_cons_eq in H;
  intro; elim H; right; auto.
inversion H1; repeat rewrite H3; auto.
Qed.

Lemma bucket_sort_L_permut:
forall Omega Gamma w G Gamma',
  L_to_Hyb_ctx Omega Gamma w = (G, Some (w, Gamma')) ->
  bucket_sort_L Omega Gamma *=* (w, Gamma') :: G.
unfold L_to_Hyb_ctx; intros;
remember (bucket_sort_L Omega Gamma) as G';
generalize dependent Omega;
generalize dependent Gamma;
generalize dependent w;
generalize dependent G;
generalize dependent Gamma';
induction G'; intros; [ | destruct a];
inversion H; subst; case_if;
inversion H1; subst; permut_simpl; rew_app;
inversion H1; subst; clear H1;
rewrite <- H3 in H;
symmetry in H; rewrite surjective_pairing in H; symmetry in H;
destruct Omega; simpl in HeqG';
[ discriminate; inversion HeqG'; subst |];
apply IHG' with (Gamma:=Gamma) (Omega :=Omega);
[rewrite <- H3; rewrite <- surjective_pairing |
 inversion HeqG'; subst]; auto.
Qed.

Lemma bucket_sort_L_smaller:
forall Omega Gamma w v t,
  ~ Mem w Omega ->
  bucket_sort_L Omega ((w, (v, t))::Gamma) =
  bucket_sort_L Omega Gamma.
induction Omega; intros; simpl; auto; case_if;
[elim H; apply Mem_here|
 rewrite IHOmega; auto; intro; elim H; rewrite Mem_cons_eq; right; auto].
Qed.

Lemma ok_Omega_to_ok_Hyb_worlds:
forall Omega Omega' Gamma w G Gamma',
  ok_Omega_L (Omega'++Omega) ->
  L_to_Hyb_ctx Omega Gamma w = (G, Some (w, Gamma')) ->
  ok_Hyb ((w, Gamma')::G) Omega'.
intros;
apply ok_Hyb_permut_any0 with (G1:=bucket_sort_L Omega Gamma);
[apply bucket_sort_L_permut; auto |];
clear H0 w G Gamma'; generalize dependent Gamma;
generalize dependent Omega';
induction Omega; intros; simpl in *; constructor.
apply ok_Omega_L_permut with (O2:=a::Omega'++Omega) in H;
[ destruct H; intro; elim H; rewrite Mem_app_or_eq; left; auto |
  permut_simpl].
apply IHOmega; apply ok_Omega_L_permut with (O1:=Omega'++a::Omega);
[rew_app; permut_simpl | ]; auto.
Qed.

Lemma flat_map_bucket_sort_L:
forall Omega Gamma w v t,
  Mem w Omega ->
  ok_Omega_L Omega ->
  flat_map snd_ (bucket_sort_L Omega ((w, (v, t)) :: Gamma)) *=*
  (v, t) :: (flat_map snd_ (bucket_sort_L Omega Gamma)).
induction Omega; intros;
[rewrite Mem_nil_eq in H; contradiction |
 rewrite Mem_cons_eq in H; destruct H ]; subst; simpl in *; case_if; rew_app;
destruct H0; permut_simpl; rew_app;
[rewrite bucket_sort_L_smaller | contradiction | rewrite IHOmega]; auto.
Qed.

Lemma ok_Gamma_to_ok_Hyb_terms:
forall Gamma Omega w G Gamma' U,
  ok_Omega_L Omega ->
  ok_Gamma_L Gamma U ->
  L_to_Hyb_ctx Omega Gamma w = (G, Some (w, Gamma')) ->
  ok_Hyb (flat_map snd_ ((w, Gamma')::G)) U.
intros;
apply ok_Hyb_permut_any0 with (G1:= flat_map snd_ (bucket_sort_L Omega Gamma));
[apply flat_map_snd_permut; apply bucket_sort_L_permut; auto |];
clear H1 Gamma' G;
generalize dependent U;
generalize dependent w;
generalize dependent Gamma;
induction Omega; [intros; simpl in *; constructor | ];
intro Gamma;
generalize dependent a;
generalize dependent Omega;
induction Gamma; intros; simpl in *;
[ rew_app; apply IHOmega; destruct H; auto | ];
destruct a; destruct p; destruct H; destruct H0; case_if; rew_app;
[constructor; auto; rewrite bucket_sort_L_smaller; auto | ];
destruct (Mem_dec var Omega v); [apply eq_var_dec | |].
apply ok_Hyb_permut_any0 with (G1 := (v0,t)::gather_keys_L a0 Gamma ++
                               flat_map snd_ (bucket_sort_L Omega Gamma));
[permut_simpl; rew_app; rewrite flat_map_bucket_sort_L; auto |
 constructor; auto; apply IHGamma].
rewrite bucket_sort_L_smaller; auto; apply IHGamma; intros;
[apply IHOmega | split |  | apply ok_Gamma_L_weakening_used with (u:=v0)]; auto.
Qed.

Lemma ok_L_to_Hyb_ctx_ok_Hyb:
forall Omega Gamma w G Gamma',
  ok_L Omega Gamma ->
  L_to_Hyb_ctx Omega Gamma w = (G, Some (w, Gamma')) ->
  ok_Bg_Hyb ((w, Gamma')::G). (* FIXME: rename ok_Bg_Hyb to ok_Hyb *)
unfold ok_L; unfold ok_Bg_Hyb; unfold L_to_Hyb_ctx;
intros; destruct H; split;
[eapply ok_Omega_to_ok_Hyb_worlds |
 eapply ok_Gamma_to_ok_Hyb_terms]; eauto.
Qed.

Lemma split_at_Hyb_fst_same:
forall Omega Gamma w v A,
  ok_Omega_L Omega ->
   fst
     (split_at_Hyb (bucket_sort_L Omega ((w, (v, A)) :: Gamma)) w) =
   fst (split_at_Hyb (bucket_sort_L Omega Gamma) w).
induction Omega; intros; simpl; auto; repeat case_if; simpl;
inversion H; subst;
[apply bucket_sort_L_smaller | rewrite IHOmega]; auto.
Qed.

Lemma split_at_Hyb_snd_cons:
forall Omega Gamma w v A Delta,
  ok_Omega_L Omega ->
  snd (split_at_Hyb (bucket_sort_L Omega Gamma) w) = Some (w, Delta) ->
  snd (split_at_Hyb (bucket_sort_L Omega ((w, (v, A)) :: Gamma)) w) =
  Some (w, (v,A)::Delta).
induction Omega; intro; induction Gamma; intros; simpl in *;
inversion H0; subst; repeat case_if; destruct H; simpl in *;
inversion H0; subst; auto.
Qed.

Lemma split_at_Hyb_cons:
forall Omega Gamma (w: var) G_Hyb Gamma_Hyb A v w,
   ok_Omega_L Omega ->
   split_at_Hyb (bucket_sort_L Omega Gamma) w =
       (G_Hyb, Some (w, Gamma_Hyb)) ->
   split_at_Hyb (bucket_sort_L Omega ((w, (v, A))::Gamma)) w =
       (G_Hyb, Some (w, (v, A)::Gamma_Hyb)).
intros; symmetry; rewrite surjective_pairing; symmetry;
rewrite split_at_Hyb_fst_same; auto;
symmetry in H0; rewrite surjective_pairing in H0; symmetry in H0;
inversion H0; subst;
rewrite split_at_Hyb_snd_cons with (Delta:=Gamma_Hyb); auto.
Qed.

Lemma gather_keys_L_fresh:
forall l w,
  ~ Mem w (map fst l) ->
  gather_keys_L w l = nil.
induction l; intros; rew_map in *; simpl in *; auto.
destruct a; case_if; simpl in *.
elim H; apply Mem_here.
rewrite IHl; auto; intro; elim H; rewrite Mem_cons_eq; right; auto.
Qed.

(* Term conversion: function *)

Fixpoint L_to_Hyb_term (w: vwo) (M0: te_L) : te_Hyb :=
match M0 with
| hyp_L v => hyp_Hyb v
| lam_L A M => lam_Hyb A (L_to_Hyb_term w M)
| appl_L M1 M2 => appl_Hyb (L_to_Hyb_term w M1) (L_to_Hyb_term w M2)
| box_L M => box_Hyb (L_to_Hyb_term (bwo 0) M)
| unbox_L M =>  unbox_fetch_Hyb w (L_to_Hyb_term w M)
| here_L M => get_here_Hyb w (L_to_Hyb_term w M)
| letd_L M1 M2 => letdia_get_Hyb w (L_to_Hyb_term w M1)
                          (L_to_Hyb_term (shift_vwo w) M2)
| fetch_L w' M => letdia_get_Hyb w' (get_here_Hyb w' (L_to_Hyb_term w' M))
                          (box_Hyb (unbox_fetch_Hyb (bwo 1) (hyp_Hyb (bte 0))))
| get_L w' M => letdia_get_Hyb w' (L_to_Hyb_term w' M)
                               (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0)))
end.

Lemma L_to_Hyb_term_subst_t:
forall M w C1 C2 v,
  (forall w, L_to_Hyb_term w C1 = C2) ->
  L_to_Hyb_term w (subst_t_L C1 v M) =
  subst_t_Hyb C2 v (L_to_Hyb_term w M).
induction M; intros; simpl in *; repeat case_if;
try erewrite IHM || (erewrite IHM1; try erewrite IHM2); eauto;
destruct v0; simpl in *; inversion H0.
Qed.

Lemma L_to_Hyb_term_subst_w:
forall M w,
  forall w0 w1 w',
    (w' = if eq_vwo_dec w w0 then w1 else w) ->
    subst_w_Hyb w1 w0 (L_to_Hyb_term w M) =
    L_to_Hyb_term w' (subst_w_L M w1 w0).
induction M; intros; simpl in *; auto.
erewrite IHM; eauto.
erewrite IHM1; try erewrite IHM2; eauto.
erewrite IHM; case_if; eauto; destruct w0; simpl in *; inversion H0; omega.
erewrite IHM; case_if; subst; eauto.
erewrite <- IHM; [ | eauto]; repeat case_if; subst; eauto;
destruct w0; simpl in *; inversion H0 || inversion H1; omega.
erewrite IHM1; try erewrite IHM2; repeat case_if; subst; eauto;
destruct w; destruct w0; simpl in *; inversion H0; subst; elim H1; auto.
erewrite IHM; case_if; subst; eauto.
erewrite <- IHM; [ | eauto]; repeat case_if; subst; eauto;
destruct w0; simpl in *;
(inversion H0 || inversion H1 || inversion H2); subst.
Qed.

Lemma L_to_Hyb_typing:
forall Omega_L Gamma_L M_L A w_L G_Hyb Gamma_Hyb,
  L_to_Hyb_ctx Omega_L Gamma_L w_L = (G_Hyb, Some (w_L, Gamma_Hyb)) ->
  Omega_L; Gamma_L |- M_L ::: A @ w_L ->
  G_Hyb |= (w_L, Gamma_Hyb) |- (L_to_Hyb_term (fwo w_L) M_L) ::: A.
unfold L_to_Hyb_ctx; intros;
generalize dependent G_Hyb;
generalize dependent Gamma_Hyb.
induction H0; intros; simpl in *.
(* hyp *)
constructor;
[apply ok_L_to_Hyb_ctx_ok_Hyb with (Omega:=Omega) (Gamma:=Gamma) (w:=w)| ];
auto; eapply Mem_L_to_Hyb_ctx; eauto.
(* lam *)
apply t_lam_Hyb with (L:=L);
[eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto | intros]; unfold open_t_Hyb in *;
unfold open_t_L in *.
rewrite <- L_to_Hyb_term_subst_t with (C1:=hyp_L (fte v')); auto;
apply H with (x:=v'); auto;
destruct Ok; apply split_at_Hyb_cons; auto.
(* appl *)
apply t_appl_Hyb with (A:=A);
[eapply ok_L_to_Hyb_ctx_ok_Hyb |
 apply IHtypes_L1 | apply IHtypes_L2]; eauto.
(* box *)
apply t_box_Hyb with (L:=L \u
                           from_list (map fst Gamma)).
assert (G_Hyb & (w, Gamma_Hyb) ~=~ (w, Gamma_Hyb) :: G_Hyb) as HP
  by PPermut_Hyb_simpl; rewrite HP;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
intros; unfold open_w_L in *; unfold open_w_Hyb in *;
assert ( G_Hyb & (w, Gamma_Hyb) ~=~ bucket_sort_L Omega Gamma) by
  (apply permut_PPermut_Hyb;
   symmetry; rewrite bucket_sort_L_permut with
            (w:=w) (Gamma':=Gamma_Hyb) (G:=G_Hyb); [permut_simpl | ]; auto);
rewrite H2;
rewrite L_to_Hyb_term_subst_w with (w':=fwo w'); try case_if; auto;
eapply H; eauto;
case_if; destruct Ok;
rewrite gather_keys_L_fresh; [|apply notin_Mem]; eauto.
(* unbox *)
apply t_unbox_Hyb; auto;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
(* fetch *)
destruct (eq_var_dec w w'); subst.
(* = *)
apply t_letdia_Hyb with (L_w:=used_w_vars_Hyb (G_Hyb & (w', Gamma_Hyb)))
                        (L_t:=used_t_vars_Hyb (G_Hyb & (w', Gamma_Hyb)))
                        (A:=[*]A);
[eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto | | intros];
unfold open_w_Hyb in *; unfold open_t_Hyb in *;
simpl in *; repeat case_if.
constructor;
[eapply ok_L_to_Hyb_ctx_ok_Hyb | ]; eauto.
apply t_box_Hyb with (L:=\{w'0} \u used_w_vars_Hyb ((w', Gamma_Hyb) :: G_Hyb)).
rew_app; apply ok_Bg_Hyb_fresh_wo_te; auto;
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb) :: G_Hyb) as HP
  by PPermut_Hyb_simpl; rewrite HP;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
intros; unfold open_w_Hyb; simpl; case_if;
apply t_unbox_fetch_Hyb with (G:=G_Hyb & (w', Gamma_Hyb))
                               (Gamma := (v', [*]A) :: nil).
apply ok_Bg_Hyb_fresh_wo_te; auto;
assert (G_Hyb & (w', Gamma_Hyb) & (w'1, nil)  ~=~
              (w'1, nil) :: ((w', Gamma_Hyb) :: G_Hyb)) as HP
  by PPermut_Hyb_simpl;
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb) :: G_Hyb) as HP2
  by PPermut_Hyb_simpl.
rewrite HP; apply ok_Bg_Hyb_fresh_wo; [eapply ok_L_to_Hyb_ctx_ok_Hyb|]; eauto.
rewrite HP2 in H2; rewrite HP; simpl in *;
repeat rewrite notin_union in *; repeat split;
destruct H2; destruct H3; destruct H6;
rewrite notin_singleton in *; eauto.
rewrite HP; rewrite HP2 in H1; simpl in *; rew_map; simpl;
rewrite from_list_nil; rewrite union_empty_l; auto.
constructor; auto.
apply ok_Bg_Hyb_fresh_wo_te; auto;
assert (G_Hyb & (w', Gamma_Hyb) & (w'1, nil)  ~=~
              (w'1, nil) :: ((w', Gamma_Hyb) :: G_Hyb)) as HP
  by PPermut_Hyb_simpl;
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb) :: G_Hyb) as HP2
  by PPermut_Hyb_simpl.
rewrite HP; apply ok_Bg_Hyb_fresh_wo; [eapply ok_L_to_Hyb_ctx_ok_Hyb|]; eauto.
rewrite HP2 in H2; rewrite HP; simpl in *;
repeat rewrite notin_union in *; repeat split;
destruct H2; destruct H3; destruct H6;
rewrite notin_singleton in *; eauto.
rewrite HP; rewrite HP2 in H1; simpl in *; rew_map; simpl;
rewrite from_list_nil; rewrite union_empty_l; auto.
apply Mem_here.
PPermut_Hyb_simpl.
(* <> *)
assert (exists G0, exists Gamma0,
          split_at_Hyb (bucket_sort_L Omega Gamma) w = (G0, Some (w, Gamma0))).
  exists (fst (split_at_Hyb (bucket_sort_L Omega Gamma) w)).
  assert (exists Gamma1, snd (split_at_Hyb (bucket_sort_L Omega Gamma) w) =
                 Some (w, Gamma1)).
  apply L_to_Hyb_ctx_Mem_Some.
  apply types_L_Mem_Omega in H0; auto.
  destruct H1; exists x; rewrite <- H1; apply surjective_pairing.
destruct H1 as (Gw, (Gammaw, H1)).
assert ((w, Gammaw) :: Gw *=* (w', Gamma_Hyb) :: G_Hyb).
transitivity (bucket_sort_L Omega Gamma); [symmetry | ];
  apply bucket_sort_L_permut; eauto.
assert (exists hd, exists tl, G_Hyb = hd & (w, Gammaw) ++ tl).
apply permut_neq_split with (l1:=(w, Gammaw)::Gw) (b:=(w', Gamma_Hyb)); auto.
intro nn; inversion nn; subst; elim n; auto. apply Mem_here.
destruct H3 as (hd, (tl, H3)).
assert ((w, Gammaw) :: (hd ++ tl) & (w', Gamma_Hyb) ~=~
                    (w, Gammaw)::Gw).
transitivity (G_Hyb & (w', Gamma_Hyb));
[subst; PPermut_Hyb_simpl| ]; apply permut_PPermut_Hyb; symmetry;
rewrite H2; permut_simpl.
apply t_letdia_get_Hyb with (L_w:=used_w_vars_Hyb (G_Hyb & (w', Gamma_Hyb)))
                            (L_t:=used_t_vars_Hyb (G_Hyb & (w', Gamma_Hyb)))
                            (A:=[*]A) (G:=hd++tl) (Gamma:=Gammaw).
rewrite H4; eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
constructor; auto.
rewrite H4; eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
assert ((hd ++ tl) & (w', Gamma_Hyb) ~=~ Gw).
 apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gammaw)).
 transitivity ((w, Gammaw)::Gw); [rewrite <- H4 | ]; PPermut_Hyb_simpl.
rewrite H5; eapply IHtypes_L; eauto.
Focus 2. subst; PPermut_Hyb_simpl.
intros;
unfold open_w_Hyb in *; unfold open_t_Hyb in *;
simpl in *; repeat case_if.
assert ((w'0, (v', [*]A) :: nil) :: (hd ++ tl) & (w, Gammaw) ~=~
       ((w'0, (v', [*]A) :: nil) :: G_Hyb)) by (subst; PPermut_Hyb_simpl).
rewrite H7;
apply t_box_Hyb with (L:=\{w'0} \u used_w_vars_Hyb ((w', Gamma_Hyb) :: G_Hyb)).
rew_app; apply ok_Bg_Hyb_fresh_wo_te; auto;
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb) :: G_Hyb) as HP
  by PPermut_Hyb_simpl; rewrite HP;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
intros; unfold open_w_Hyb; simpl; case_if;
apply t_unbox_fetch_Hyb with (G:=G_Hyb & (w', Gamma_Hyb))
                               (Gamma := (v', [*]A) :: nil).
apply ok_Bg_Hyb_fresh_wo_te; auto;
assert (G_Hyb & (w', Gamma_Hyb) & (w'1, nil)  ~=~
              (w'1, nil) :: ((w', Gamma_Hyb) :: G_Hyb)) as HP
  by PPermut_Hyb_simpl;
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb) :: G_Hyb) as HP2
  by PPermut_Hyb_simpl.
rewrite HP; apply ok_Bg_Hyb_fresh_wo; [eapply ok_L_to_Hyb_ctx_ok_Hyb|]; eauto.
rewrite HP; rewrite HP2 in H6; simpl in *;
repeat rewrite notin_union in *; repeat split;
destruct H6; destruct H8; destruct H11;
rewrite notin_singleton in *; eauto.
rewrite HP; rewrite HP2 in H5; simpl in *; rew_map; simpl;
rewrite from_list_nil; rewrite union_empty_l; auto.
constructor; auto.
apply ok_Bg_Hyb_fresh_wo_te; auto;
assert (G_Hyb & (w', Gamma_Hyb) & (w'1, nil)  ~=~
              (w'1, nil) :: ((w', Gamma_Hyb) :: G_Hyb)) as HP
  by PPermut_Hyb_simpl;
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb) :: G_Hyb) as HP2
  by PPermut_Hyb_simpl.
rewrite HP; apply ok_Bg_Hyb_fresh_wo; [eapply ok_L_to_Hyb_ctx_ok_Hyb|]; eauto.
rewrite HP2 in H6; rewrite HP; simpl in *;
repeat rewrite notin_union in *; repeat split;
destruct H6; destruct H8; destruct H11;
rewrite notin_singleton in *; eauto.
rewrite HP; rewrite HP2 in H5; simpl in *; rew_map; simpl;
rewrite from_list_nil; rewrite union_empty_l; auto.
apply Mem_here.
PPermut_Hyb_simpl.
(* here *)
apply t_here_Hyb; auto;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
(* get *)
destruct (eq_var_dec w' w).
(* = *)
subst; apply t_letdia_Hyb with (L_w:=used_w_vars_Hyb ((w, Gamma_Hyb) :: G_Hyb))
                               (L_t:=used_t_vars_Hyb ((w, Gamma_Hyb) :: G_Hyb))
                               (A:=A);
[eapply ok_L_to_Hyb_ctx_ok_Hyb | eapply IHtypes_L| ]; eauto;
intros; unfold open_w_Hyb; unfold open_t_Hyb; simpl; repeat case_if;
assert ((w', (v', A) :: nil) :: G_Hyb & (w, Gamma_Hyb) ~=~
        (w', (v', A)::nil) :: ((w, Gamma_Hyb) :: G_Hyb))
  as H4 by PPermut_Hyb_simpl;
apply t_get_here_Hyb with (G:=G_Hyb) (Gamma:=(v', A)::nil).
rewrite H4; apply ok_Bg_Hyb_fresh_wo_te; auto;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
constructor; [ | apply Mem_here];
rewrite H4; apply ok_Bg_Hyb_fresh_wo_te; auto;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
PPermut_Hyb_simpl.
(* <> *)
assert (exists G0, exists Gamma0,
          split_at_Hyb (bucket_sort_L Omega Gamma) w = (G0, Some (w, Gamma0))).
  exists (fst (split_at_Hyb (bucket_sort_L Omega Gamma) w)).
  assert (exists Gamma1, snd (split_at_Hyb (bucket_sort_L Omega Gamma) w) =
                 Some (w, Gamma1)).
  apply L_to_Hyb_ctx_Mem_Some.
  apply types_L_Mem_Omega in H0; auto.
  destruct H1; exists x; rewrite <- H1; apply surjective_pairing.
destruct H1 as (Gw, (Gammaw, H1)).
assert ((w, Gammaw) :: Gw *=* (w', Gamma_Hyb) :: G_Hyb).
transitivity (bucket_sort_L Omega Gamma); [symmetry | ];
  apply bucket_sort_L_permut; eauto.
assert (exists hd, exists tl, G_Hyb = hd & (w, Gammaw) ++ tl).
apply permut_neq_split with (l1:=(w, Gammaw)::Gw) (b:=(w', Gamma_Hyb)); auto.
intro nn; inversion nn; subst; elim n; auto. apply Mem_here.
destruct H3 as (hd, (tl, H3)).
apply t_letdia_get_Hyb with (L_w:=used_w_vars_Hyb (G_Hyb & (w', Gamma_Hyb)))
                            (L_t:=used_t_vars_Hyb (G_Hyb & (w', Gamma_Hyb)))
                            (A:=A)(G:=hd++tl)(Gamma:=Gammaw).
assert ((w, Gammaw) :: (hd ++ tl) & (w', Gamma_Hyb) ~=~
                    (w', Gamma_Hyb) :: G_Hyb)
  by (subst; PPermut_Hyb_simpl).
rewrite H4; eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
assert ((hd ++ tl) & (w', Gamma_Hyb) ~=~ Gw).
apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gammaw)).
transitivity ((w', Gamma_Hyb) :: G_Hyb).
subst; PPermut_Hyb_simpl.
apply permut_PPermut_Hyb in H2; rewrite <- H2; PPermut_Hyb_simpl.
rewrite H4; eapply IHtypes_L; auto.
intros; unfold open_w_Hyb; unfold open_t_Hyb; simpl; repeat case_if.
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb)::G_Hyb)
  by PPermut_Hyb_simpl.
apply t_get_here_Hyb with (G:=G_Hyb) (Gamma:=(v', A)::nil).
apply ok_Bg_Hyb_fresh_wo_te; auto;
rewrite H6; eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
constructor; [ | apply Mem_here];
apply ok_Bg_Hyb_fresh_wo_te; auto.
rewrite H6; eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
PPermut_Hyb_simpl.
subst; PPermut_Hyb_simpl.
subst; PPermut_Hyb_simpl.
(* letd *)
apply t_letdia_Hyb with (L_w:=Lw \u from_list Omega \u
                                 from_list (map fst Gamma)
                              \u used_w_vars_Hyb ((w, Gamma_Hyb) :: G_Hyb))
                          (L_t:=Lt \u
                                   used_t_vars_Hyb ((w, Gamma_Hyb) :: G_Hyb))
                          (A:=A); auto;
[eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto | intros];
unfold open_w_L in *; unfold open_w_Hyb in *;
unfold open_t_L in *; unfold open_t_Hyb in *;
clear IHtypes_L HT2.
assert (G_Hyb & (w, Gamma_Hyb) ~=~ bucket_sort_L Omega Gamma) by
  (apply permut_PPermut_Hyb;
   symmetry; rewrite bucket_sort_L_permut with
            (w:=w) (Gamma':=Gamma_Hyb) (G:=G_Hyb); [permut_simpl | ]; auto).
rewrite L_to_Hyb_term_subst_w with (w':=fwo w); try case_if; auto.
rewrite <- L_to_Hyb_term_subst_t with (C1 := hyp_L (fte v'));
[ | intros; auto];
apply H with (t:=v') (w':=w'); eauto.
repeat case_if; auto.
simpl in *; repeat rewrite notin_union in *; destruct H3; destruct H5;
destruct H6; destruct H7; rewrite notin_singleton in H7;
elim H7; auto.
rewrite bucket_sort_L_smaller; [| apply notin_Mem]; eauto;
rewrite gather_keys_L_fresh; [| apply notin_Mem]; eauto;
symmetry in H1; rewrite surjective_pairing in H1; inversion H1; subst;
rewrite H8; auto.
Qed.

Lemma L_to_Hyb_term_lc_w:
forall M w n w0 k,
  (w = fwo w0 \/ (w = bwo k /\ k < n)) ->
  lc_w_n_L n M ->
  lc_w_n_Hyb n (L_to_Hyb_term w M).
induction M; intros; inversion H0; subst; simpl in *;
try destruct w; simpl in *; try constructor; try omega; eauto;
try (eapply IHM || (eapply IHM1; try eapply IHM2);
     auto; right; split; eauto; omega);
try (constructor; try omega; constructor);
try (destruct H; try discriminate; destruct H; inversion H; subst; omega);
try omega; try (constructor; omega);
try (constructor; try omega; eapply IHM; auto; left; eauto).
eapply IHM2; auto; right; split; eauto; destruct H; try discriminate;
destruct H; inversion H; subst; omega.
Grab Existential Variables.
auto. auto. auto. auto.
auto. auto. auto. auto.
auto. auto. auto. auto.
Qed.

Lemma L_to_Hyb_term_lc_w_fwo:
forall M n w,
  lc_w_n_L n M -> lc_w_n_Hyb n (L_to_Hyb_term (fwo w) M).
intros; eapply L_to_Hyb_term_lc_w; eauto.
Grab Existential Variables.
auto.
Qed.

Lemma L_to_Hyb_term_lc_w_bwo:
forall M n k,
  k < n -> lc_w_n_L n M -> lc_w_n_Hyb n (L_to_Hyb_term (bwo k) M).
assert (exists (v:var), v \notin \{}) as H1 by apply Fresh; destruct H1;
intros; eapply L_to_Hyb_term_lc_w; eauto.
Grab Existential Variables.
auto.
Qed.

Hint Resolve L_to_Hyb_term_lc_w_fwo L_to_Hyb_term_lc_w_bwo.

Lemma L_to_Hyb_term_lc_t:
forall M n w,
  lc_t_n_L n M ->
  lc_t_n_Hyb n (L_to_Hyb_term w M).
induction M; intros; simpl in *; inversion H; subst; constructor;
eauto; try omega.
constructor; constructor; omega.
constructor; constructor; constructor;  omega.
constructor; eapply IHM; auto.
Qed.

Hint Resolve L_to_Hyb_term_lc_t.

(* Term conversion: relation *)

(* Note: the relation is wider than necessary, as unbox, here and letdia
are assumed to move to *any* world, not just the current one *)
(* Special cases? (e.g. unbox (fetch w M))*)
Inductive L_to_Hyb_term_R: te_L -> te_Hyb -> Prop :=
| hyp_L_Hyb:
    forall v, L_to_Hyb_term_R (hyp_L v) (hyp_Hyb v)
| lam_L_Hyb:
    forall M N A,
      L_to_Hyb_term_R M N ->
      L_to_Hyb_term_R (lam_L A M) (lam_Hyb A N)
| appl_L_Hyb:
    forall M1 M2 N1 N2,
      L_to_Hyb_term_R M1 N1 ->
      L_to_Hyb_term_R M2 N2 ->
      L_to_Hyb_term_R (appl_L M1 M2) (appl_Hyb N1 N2)
| box_L_Hyb:
    forall M N,
      L_to_Hyb_term_R M N ->
      L_to_Hyb_term_R (box_L M) (box_Hyb N)
| unbox_L_Hyb:
    forall M N,
      L_to_Hyb_term_R M N ->
      forall w, L_to_Hyb_term_R (unbox_L M) (unbox_fetch_Hyb w N)
| here_L_Hyb:
    forall M N,
      L_to_Hyb_term_R M N ->
      forall w, L_to_Hyb_term_R (here_L M) (get_here_Hyb w N)
| letd_L_Hyb:
    forall M1 M2 N1 N2,
      L_to_Hyb_term_R M1 N1 ->
      L_to_Hyb_term_R M2 N2 ->
      forall w, L_to_Hyb_term_R (letd_L M1 M2) (letdia_get_Hyb w N1 N2)
| fetch_L_Hyb:
    forall M N w,
      L_to_Hyb_term_R M N ->
      L_to_Hyb_term_R (fetch_L w M)
                    (letdia_get_Hyb w (get_here_Hyb w N)
                          (box_Hyb (unbox_fetch_Hyb (bwo 1) (hyp_Hyb (bte 0)))))
| get_L_Hyb:
    forall M N w,
      L_to_Hyb_term_R M N ->
      L_to_Hyb_term_R (get_L w M)
                    (letdia_get_Hyb w N (get_here_Hyb (bwo 0)
                                                      (hyp_Hyb (bte 0))))
.

Lemma L_to_Hyb_term_R_subst_t:
forall M M' C1 C2 v,
  L_to_Hyb_term_R C1 C2 ->
  L_to_Hyb_term_R M M' ->
  L_to_Hyb_term_R (subst_t_L C1 v M) (subst_t_Hyb C2 v M').
intros;
generalize dependent C1; generalize dependent C2; generalize dependent v.
induction H0; intros; simpl;
try (apply letd_get_L_Hyb; auto);
repeat case_if; try constructor; auto;
destruct v; simpl in *; inversion H1.
Qed.

Lemma L_to_Hyb_term_R_subst_w:
forall M M',
    L_to_Hyb_term_R M M' ->
  forall w0 w1,
    L_to_Hyb_term_R (subst_w_L M w1 w0)
                    (subst_w_Hyb w1 w0 M').
intros M M' H; induction H; intros; simpl;
try (apply letd_get_L_Hyb; auto);
repeat case_if; try constructor; auto;
destruct w0; simpl in *; inversion H0 || inversion H1.
Qed.

Lemma L_to_Hyb_term_L_to_Hyb_term_R:
forall M w,
  L_to_Hyb_term_R M (L_to_Hyb_term w M).
induction M; intros; simpl; try constructor; auto.
Qed.
Hint Resolve L_to_Hyb_term_L_to_Hyb_term_R.

Lemma L_to_Hyb_term_R_typing:
forall M_L Omega_L Gamma_L A w_L G_Hyb Gamma_Hyb,
  L_to_Hyb_ctx Omega_L Gamma_L w_L = (G_Hyb, Some (w_L, Gamma_Hyb)) ->
  Omega_L; Gamma_L |- M_L ::: A @ w_L ->
  exists M_Hyb,
    L_to_Hyb_term_R M_L M_Hyb /\
    G_Hyb |= (w_L, Gamma_Hyb) |- M_Hyb ::: A.
intros; exists (L_to_Hyb_term (fwo w_L) M_L); split;
[apply L_to_Hyb_term_L_to_Hyb_term_R |
 eapply L_to_Hyb_typing; eauto].
Qed.

Lemma L_to_Hyb_term_R_lc_t:
forall M M' n,
  lc_t_n_L n M ->
  L_to_Hyb_term_R M M' ->
  lc_t_n_Hyb n M'.
intros; generalize dependent n; induction H0;
intros; inversion H; subst; constructor; eauto.
constructor; constructor; constructor; omega.
constructor; eauto.
constructor; constructor; omega.
Qed.

Hint Resolve L_to_Hyb_term_R_lc_t.

(* A mixture of both relation and function *)

Lemma L_to_Hyb_term_R_value:
forall M M',
 lc_w_Hyb M' -> lc_t_Hyb M' ->
  value_L M -> L_to_Hyb_term_R M M' ->
  value_Hyb M' \/
  forall w, exists M'', steps_Hyb (M', w) (M'', w) /\ value_Hyb M''.
intros; generalize dependent M'; induction H1; intros;
inversion H2; subst.
left; constructor.
left; constructor.
inversion H; inversion H7; subst; [ | assert (False); [omega | contradiction]];
inversion H0; subst; inversion H2; inversion H4; subst;
inversion H11; inversion H9; subst;[ | assert (False); [omega | contradiction]].
 destruct IHvalue_L with (M':=N1); auto; right; intros.
(* value *)
eexists; split.
constructor; constructor; auto;
try (inversion H0; inversion H; subst; auto).
unfold open_w_Hyb; unfold open_t_Hyb; simpl; repeat case_if;
constructor; auto.
(* step *)
specialize H3 with (fwo w2); destruct H3 as (N2, (H3, H5)).
apply steps_Hyb_letdia_here with (w1:=w) (w:=fwo w0)
      (M':= (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0)))) in H3; eauto.
exists ((get_here_Hyb (bwo 0) (hyp_Hyb (bte 0)) ^w^ (fwo w2) ) ^t^ N2); split.
auto.
unfold open_w_Hyb in *; unfold open_t_Hyb in *; simpl in *; repeat case_if;
econstructor; eauto.
Qed.

Lemma L_to_Hyb_term_value:
forall M M' w,
 lc_w_Hyb M' -> lc_t_Hyb M' ->
  value_L M -> (M' = L_to_Hyb_term w M) ->
  value_Hyb M' \/
  exists M'', steps_Hyb (M', w) (M'', w) /\ value_Hyb M''.
intros.
destruct L_to_Hyb_term_R_value with M M'; subst; eauto.
Qed.

Fixpoint has_fetch_L (M0: te_L) :=
match M0 with
| hyp_L v => False
| lam_L A M => has_fetch_L M
| appl_L M N => has_fetch_L M \/ has_fetch_L N
| box_L M => has_fetch_L M
| unbox_L M => has_fetch_L M
| here_L M => has_fetch_L M
| letd_L M N  => has_fetch_L M \/ has_fetch_L M
| get_L w M => has_fetch_L M
| fetch_L w M => True
end.

(*
Alt. formulation:
forall M N,
  ~ has_fetch_L M ->
  L_to_Hyb_term_R M N ->
  forall M' w, step_L (M, w) (M', w) ->
    exists N', L_to_Hyb_term_R M' N' /\ steps_Hyb (N, w) (N', w).

   This lemma is too weak as we have no way of knowing that this N ' is
   actually simply L_to_Hyb_term w M' -- and since not all of pairs
   in R preserve types, this gives us nothing.

   Another problem: for unbox, we have
      R M N -> forall w, R (unbox M) (unbf w N),
   Say we have
   R (unbox M) (unbf w1 N0)
   R M N0
   M, w |-> M'0, w
   N'0 is such that
      N0, w |->* N'0, w
      R M'0 N'0
   What is N'?
   It has to be that (unbf w1 N), w |->* N', w, so N' is of the form "unbf w1 X"
   At the same time, R (unbox M'0) (unbf w1 X) - so R M'0 X.
   Finally N' = unbf w1 N'0
   BUT: how do we prove that (unbf w1 N), w |->* (unbf w1 N'0), w?
   It requires that N, w1 |->* N'0, w1. But this is not the case.

   Idea: can we add typing as a condition and the N' that exists has
   to also preserve typing?

*)

(*
Alt. formulation:
forall M M' w,
  ~ has_fetch_L M ->
  step_L (M, w) (M', w) ->
  steps_Hyb (L_to_Hyb_term w M, w) (L_to_Hyb_term w M', w).

   For beta reduction (and reduction for letdia-here) we need to be able to
   say steps_Hyb (appl (lam a (f w M)) (f w N), w) (f w (open_L M N))
   and we cannot move f w (open M N) = open (f w M) (f w N), because
   lemma for subst_t rewrites requires basically (forall w0, f w0 M = f w M)
   -- and we do not have that.
*)

(*
Alt. formulation:
forall M N M' N' w,
  ~ has_fetch_L M ->
  step_L (M, w) (M', w) ->
  L_to_Hyb_term_R M N ->
  L_to_Hyb_term_R M' N' ->
  steps_Hyb (N, w) (N', w).

   In order to prove this we need to be able to conclude:
   N' = open_t_Hyb N N2
   from:
   L_to_Hyb_term_R (open_t_L M M2) N',
   L_to_Hyb_term_R M N,
   L_to_Hyb_term_R M2 N2
   (e.g. for beta-reduction) and this is simply not true,
   as we cannot conclude
   R M N /\ R M N' -> N = N' and this is what we are actually asking for.
*)

(* Note: first try to prove the silly version, then make it useful *)
Lemma L_to_Hyb_steps:
forall M M' w,
  lc_w_L M -> lc_t_L M ->
  ~ has_fetch_L M ->
  step_L (M, fwo w) (M', fwo w) ->
  exists N,
    L_to_Hyb_term_R M N /\ lc_w_Hyb N /\
    exists N',
      L_to_Hyb_term_R M' N' /\
      steps_Hyb (N, fwo w) (N', fwo w).
induction M; intros; inversion H2; subst.
(* appl-lam *)
exists (L_to_Hyb_term (fwo w) (appl_L (lam_L A M) M2)); repeat split;
[apply L_to_Hyb_term_L_to_Hyb_term_R |
 eapply L_to_Hyb_term_lc_w; eauto | simpl ];
exists (open_t_Hyb (L_to_Hyb_term (fwo w) M) (L_to_Hyb_term (fwo w) M2)); split.
unfold open_t_L; unfold open_t_Hyb;
apply L_to_Hyb_term_R_subst_t;
apply L_to_Hyb_term_L_to_Hyb_term_R.
constructor; constructor.
eapply L_to_Hyb_term_lc_w; eauto; right; split; eauto; omega.
eapply L_to_Hyb_term_lc_t; eauto;
unfold open_t_L in *; apply lc_t_L_subst_t_rev in H8; auto.
eapply L_to_Hyb_term_lc_w; eauto; right; split; eauto; omega.
eapply L_to_Hyb_term_lc_t; eauto;
unfold open_t_L in *; apply lc_t_L_subst_t_rev in H8; auto.
(* appl *)
simpl in *.
destruct IHM1 with (M':=M'0) (w:=w); auto.
destruct H3; destruct H4; destruct H5; destruct H5.
exists (appl_Hyb x (L_to_Hyb_term (fwo w) M2));
repeat split; [constructor | constructor | ]; auto;
[apply L_to_Hyb_term_L_to_Hyb_term_R | ];
exists (appl_Hyb x0 (L_to_Hyb_term (fwo w) M2));
split; [constructor | ]; auto;
[apply L_to_Hyb_term_L_to_Hyb_term_R | ].
apply steps_Hyb_appl; auto.
(* unbox-box *)
exists (L_to_Hyb_term (fwo w) (unbox_L (box_L M0))); repeat split;
[apply L_to_Hyb_term_L_to_Hyb_term_R |
 eapply L_to_Hyb_term_lc_w; eauto | simpl ];
exists (open_w_Hyb (L_to_Hyb_term (bwo 0) M0) (fwo w)); split.
unfold open_w_L; unfold open_w_Hyb;
apply L_to_Hyb_term_R_subst_w;
apply L_to_Hyb_term_L_to_Hyb_term_R.
constructor; constructor.
eapply L_to_Hyb_term_lc_w; eauto;
unfold open_w_L in *; apply lc_w_L_subst_t_rev in H7; auto.
eapply L_to_Hyb_term_lc_t; eauto.
(* unbox *)
simpl in *; destruct IHM with (M':=M'0) (w:=w); auto;
destruct H3; destruct H4; destruct H5; destruct H5.
exists (unbox_fetch_Hyb (fwo w) x);
repeat split; [constructor | constructor |]; auto;
exists (unbox_fetch_Hyb (fwo w) x0);
split; [constructor | ]; auto;
apply steps_Hyb_unbox; eauto.
eapply L_to_Hyb_term_R_lc_t; eauto.
(* get *)
destruct v; inversion H; subst; try omega; simpl in *.
destruct IHM with (M'0) v; auto.
destruct H3 as (H3, (H4, (x0, (H9, H10)))).
exists (letdia_get_Hyb (fwo v)
        x (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0))));
repeat split; [constructor | constructor |]; auto;
[constructor; constructor; try omega |].
exists (letdia_get_Hyb (fwo v)
        x0 (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0))));
split; [constructor | ]; auto.
eapply steps_Hyb_get; eauto.
eapply L_to_Hyb_term_R_lc_t; eauto.
constructor; auto. constructor; auto.
(* get-get *)
(*
destruct v; inversion H; subst; try omega; simpl in *;
destruct w'; inversion H6; subst; try omega; simpl in *;
inversion H0; inversion H8; inversion H4; subst;
inversion H7; inversion H12; subst.
apply L_to_Hyb_value with (M':= L_to_Hyb_term (fwo v0) M2) in HT;
[| eapply L_to_Hyb_term_lc_w | eapply L_to_Hyb_term_lc_t |
 apply L_to_Hyb_term_L_to_Hyb_term_R]; eauto; destruct HT.
(* value *)

assert (step_Hyb ((letdia_get_Hyb (fwo v0)
           (get_here_Hyb (fwo v0) (L_to_Hyb_term (fwo v0) M2))
           (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0)))), fwo v)
    (((get_here_Hyb (bwo 0) (hyp_Hyb (bte 0))) ^w^ (fwo v0)) ^t^
        (L_to_Hyb_term (fwo v0) M2), fwo v)).
  constructor.
  eapply L_to_Hyb_term_lc_w; eauto.
  eapply L_to_Hyb_term_lc_t; eauto.
  constructor; [constructor | omega].
  constructor; constructor; omega.
  auto.
unfold open_w_Hyb in *; unfold open_t_Hyb in *; simpl in *;
repeat case_if.
apply red_letdia_get_Hyb with (ctx':=fwo w)
  (N:=(get_here_Hyb (bwo 0) (hyp_Hyb (bte 0))))in H5.
Focus 2.
constructor; constructor; try omega; try constructor;
eapply L_to_Hyb_term_lc_w; eauto.
Focus 2.
constructor; constructor; try constructor; try omega;
eapply L_to_Hyb_term_lc_t; eauto.
Focus 2.
constructor; constructor.
Focus 2.
constructor; constructor; omega.
exists (L_to_Hyb_term (fwo w) (get_L (fwo v) (get_L (fwo v0) (here_L M2))));
repeat split;
[apply L_to_Hyb_term_L_to_Hyb_term_R | eapply L_to_Hyb_term_lc_w; eauto |];
simpl.
exists (letdia_get_Hyb (fwo v)
              (get_here_Hyb (fwo v0) (L_to_Hyb_term (fwo v0) M2))
              (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0)))); split.
Focus 2. constructor; auto.
constructor; constructor; apply L_to_Hyb_term_L_to_Hyb_term_R.
exists (L_to_Hyb_term (fwo v0) (get_L (fwo v0) (here_L M2)));
split; [apply L_to_Hyb_term_L_to_Hyb_term_R | ].
simpl.
Note: make special case in the function (and relation) for get-get?
*)
skip.
(* letdia-here *)
inversion H; inversion H0; subst;
destruct w'; inversion H12; inversion H17; try omega; subst;
inversion H5; inversion H18; subst;
exists (L_to_Hyb_term (fwo w) (letd_L (get_L (fwo v) (here_L M)) M2));
repeat split;
[apply L_to_Hyb_term_L_to_Hyb_term_R |
 eapply L_to_Hyb_term_lc_w; eauto | simpl ].
exists (((L_to_Hyb_term (fwo v) M2) ^w^ (fwo v)) ^t^ (L_to_Hyb_term (fwo v) M));
split.
unfold open_w_L; unfold open_w_Hyb; unfold open_t_L; unfold open_t_Hyb;
apply L_to_Hyb_term_R_subst_t; [apply L_to_Hyb_term_L_to_Hyb_term_R |];
apply L_to_Hyb_term_R_subst_w; apply L_to_Hyb_term_L_to_Hyb_term_R.
apply L_to_Hyb_value with (M':= L_to_Hyb_term (fwo v) M) in H11;
[| eapply L_to_Hyb_term_lc_w | eapply L_to_Hyb_term_lc_t |
 apply L_to_Hyb_term_L_to_Hyb_term_R]; eauto; destruct H11.
(* value *)
assert ((letdia_get_Hyb (fwo v)
           (get_here_Hyb (fwo v) (L_to_Hyb_term (fwo v) M))
           (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0))), fwo w) |->
        (((get_here_Hyb (bwo 0) (hyp_Hyb (bte 0)))^w^ (fwo v)) ^t^
          (L_to_Hyb_term (fwo v) M), fwo w)).
constructor. skip. skip. skip. skip. auto.
unfold open_w_Hyb in *; unfold open_t_Hyb in *; simpl in *;
repeat case_if.
assert (
    (letdia_get_Hyb (fwo w) (get_here_Hyb (fwo v) (L_to_Hyb_term (fwo v) M))
                     (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0))), fwo w) |->
     (((get_here_Hyb (bwo 0) (hyp_Hyb (bte 0))) ^w^ (fwo v)) ^t^
      (L_to_Hyb_term (fwo v) M),
      fwo w)).
constructor. skip. skip. skip. skip. auto.
unfold open_w_Hyb in *; unfold open_t_Hyb in *; simpl in *;
repeat case_if.
(*
exists (letdia_get_Hyb (fwo v0)
        (L_to_Hyb_term (fwo v) (get_L (fwo v0) M0))
        (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0)))).
assert (L_to_Hyb_term_R (get_L (fwo v0) M0)

repeat split; simpl. constructor. | constructor |]; auto.
[constructor; constructor; try omega |];
exists (letdia_get_Hyb (fwo v0)
        x0 (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0))));
split; [constructor | ]; auto;
eapply steps_Hyb_get; eauto;
[eapply L_to_Hyb_term_R_lc_t in H3; eauto | |];
constructor; auto.
inversion H2.
destruct IHM with M0 v; auto.
destruct H3 as (H3, (H4, (x0, (H9, H10))));
exists (letdia_get_Hyb (fwo v0)
        x (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0))));
repeat split; [constructor | constructor |]; auto;
[constructor; constructor; try omega |];
exists (letdia_get_Hyb (fwo v0)
        x0 (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0))));
split; [constructor | ]; auto;
eapply steps_Hyb_get; eauto;
[eapply L_to_Hyb_term_R_lc_t in H3; eauto | |];
constructor; auto.

(*
forall M N,
  lc_t_Hyb N -> lc_w_Hyb N ->
  ~ has_fetch_L M ->
  L_to_Hyb_term_R M N ->
  forall M' w, step_L (M, w) (M', w) ->
    exists N' w', L_to_Hyb_term_R M' N' /\
               steps_Hyb (N, w') (N', w')
.
(* try: induction M *)
induction M; intros; inversion H2; inversion H3; subst; simpl in *.
(* appl-lam *)
inversion H6; subst;
inversion H; inversion H0; inversion H10; inversion H19; subst.
exists (open_t_Hyb N N2); exists w;
split;
[unfold open_t_L in *; unfold open_t_Hyb in *; apply L_to_Hyb_term_R_subst_t |
 constructor; constructor ]; auto.
(* appl *)
inversion H; inversion H0; subst.
destruct IHM1 with N1 M'0 w; auto; try (intro; elim H; left; auto);
destruct H4; destruct H4;
exists (appl_Hyb x N2); exists x0; split; [constructor; auto |];
apply steps_Hyb_appl; auto.
(* unbox-box *)
inversion H5; subst.
destruct w0; inversion H; inversion H0; subst; try omega;
inversion H8; inversion H14; subst.
exists (open_w_Hyb N w); exists w; split;
[unfold open_w_L in *; unfold open_w_Hyb in *; apply L_to_Hyb_term_R_subst_w |
 constructor; constructor]; auto.
(* unbox *)
destruct w0; inversion H; inversion H0; try omega; subst.
destruct IHM with N0 M'0 w; auto. destruct H4; destruct H4.
exists (unbox_fetch_Hyb (fwo v) x); exists (fwo v); split;
[constructor; auto | ];
apply steps_Hyb_unbox; auto.
(* try: induction on step_L M M' *)
intros.
generalize dependent G.
generalize dependent Gamma.
generalize dependent Omega.
generalize dependent Delta.
generalize dependent A.
generalize dependent N.
remember (M, fwo w) as M0; generalize dependent M;
remember (M', fwo w) as M'0; generalize dependent M'.
generalize dependent w.
induction H4; intros; inversion HeqM0; inversion HeqM'0; subst;
simpl in *.
(* appl-lam *)
inversion H4; inversion H10; subst.
exists (open_t_Hyb N3 N2);
repeat split;
[unfold open_t_L in *; unfold open_t_Hyb in *; apply L_to_Hyb_term_R_subst_t |
 constructor; constructor ]; auto.
skip. skip. skip. skip. (* lc! *)
(* unbox-box *)
inversion H2; inversion H7; subst.
exists (open_w_Hyb N1 (fwo w0)); split;
[unfold open_w_L in *; unfold open_w_Hyb in *; apply L_to_Hyb_term_R_subst_w |
 constructor; constructor]; auto. skip. skip. (* lc !*)
(* letdia-here *)
inversion H5; inversion H11; inversion H18; subst.
apply L_to_Hyb_value with (M':= N4) in H3; destruct H3.
(* value *)
exists (open_t_Hyb (open_w_Hyb N2 w') N4); split.
unfold open_t_L in *; unfold open_t_Hyb in *; apply L_to_Hyb_term_R_subst_t;
auto; unfold open_w_L in *; unfold open_w_Hyb in *;
apply L_to_Hyb_term_R_subst_w; auto.
assert (((letdia_get_Hyb w' (get_here_Hyb w2 N4)
           (get_here_Hyb (bwo 0) (hyp_Hyb (bte 0)))), w) |->
     ((get_here_Hyb (bwo 0) (hyp_Hyb (bte 0)) ^w^ w2 ) ^t^ N4, w))
by (constructor; try repeat constructor; try omega; auto; skip);
unfold open_t_Hyb in H7; unfold open_w_Hyb in H7; simpl in *; repeat case_if.
apply multi_step_Hyb with (M':=letdia_get_Hyb w (get_here_Hyb w2 N4) N2).
constructor. auto.
skip. skip. skip. skip.
constructor. constructor.

replace ((get_here_Hyb (bwo 0) (hyp_Hyb (bte 0)) ^w^ w2 ) ^t^ N4) with
  (get_here_Hyb w2 N4) by
    (unfold open_w_Hyb; unfold open_t_Hyb; simpl; repeat case_if; auto).
constructor.
(* finite steps *)
constructor. constructor.
(* appl *)
destruct IHM1 with N1 M'0 w; auto; try (intro; elim H; left; auto);
destruct H2; exists (appl_Hyb x N2); split; [constructor; auto |];
apply steps_Hyb_appl; auto.
(* unbox *)
destruct IHM with N0 M'0 w; auto; destruct H2.
exists (unbox_fetch_Hyb w1 x); split; [constructor; auto | ].
apply steps_Hyb_unbox; auto.
(* try: induction on step_L M M' *)
intros.
generalize dependent N.
remember (M, w) as M0; generalize dependent M;
remember (M', w) as M'0; generalize dependent M';
generalize dependent w.
induction H1; intros; inversion HeqM0; inversion HeqM'0; subst;
simpl in *.

(* try: induction on R M N *)
Admitted.
*)
*)
Admitted.

Close Scope labeled_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
