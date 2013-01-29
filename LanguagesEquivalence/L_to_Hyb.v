Add LoadPath "..".
Add LoadPath "../Labeled/Lists".
Add LoadPath "../Hybrid".

Require Import Shared.
Require Import Labeled.
Require Import Hybrid.

Open Scope is5_scope.
Open Scope permut_scope.
Open Scope labeled_is5_scope.
Open Scope hybrid_is5_scope.

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
unfold L_to_Hyb_ctx. intros.
remember (bucket_sort_L Omega Gamma) as l.
generalize dependent Omega; generalize dependent Gamma.
generalize dependent w;
induction l; intros.
destruct Omega; simpl in *;
[rewrite Mem_nil_eq in H; contradiction | inversion Heql].
destruct a; simpl; case_if; simpl.
eexists; auto.
destruct Omega; simpl in *; inversion Heql; subst.
apply IHl with (Gamma0:=Gamma) (Omega0:=Omega) (w:=w); auto.
rewrite Mem_cons_eq in H; destruct H; contradiction || auto.
Qed.

Lemma Mem_gather_keys_L:
forall Gamma w v A,
  Mem (w, (v, A)) Gamma ->
  Mem (v,A) (gather_keys_L w Gamma).
induction Gamma; intros.
rewrite Mem_nil_eq in H; contradiction.
destruct a; destruct p; rewrite Mem_cons_eq in H; destruct H; simpl.
inversion H; subst; case_if; apply Mem_here.
case_if; [rewrite Mem_cons_eq; right | ]; apply IHGamma; auto.
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
unfold L_to_Hyb_ctx. intros.
remember (bucket_sort_L Omega Gamma) as G'.
generalize dependent Omega.
generalize dependent Gamma.
generalize dependent w.
generalize dependent G.
generalize dependent Gamma'.
induction G'; intros; [ | destruct a];
inversion H; subst; case_if;
inversion H1; subst; permut_simpl; rew_app.
inversion H1; subst; clear H1.
rewrite <- H3 in H.
symmetry in H; rewrite surjective_pairing in H; symmetry in H.
destruct Omega; simpl in HeqG'. discriminate;
inversion HeqG'; subst.
apply IHG' with (Gamma:=Gamma) (Omega :=Omega).
rewrite <- H3; rewrite <- surjective_pairing; auto.
inversion HeqG'; subst; auto.
Qed.

Lemma bucket_sort_L_smaller:
forall Omega Gamma w v t,
  ~ Mem w Omega ->
  bucket_sort_L Omega ((w, (v, t))::Gamma) =
  bucket_sort_L Omega Gamma.
induction Omega; intros; simpl; auto; case_if.
elim H; apply Mem_here.
rewrite IHOmega; auto; intro; elim H; rewrite Mem_cons_eq; right; auto.
Qed.

Lemma ok_Omega_to_ok_Hyb_worlds:
forall Omega Omega' Gamma w G Gamma',
  ok_Omega_L (Omega'++Omega) ->
  L_to_Hyb_ctx Omega Gamma w = (G, Some (w, Gamma')) ->
  ok_Hyb ((w, Gamma')::G) Omega'.
intros;
apply ok_Hyb_permut_any0 with (G1:=bucket_sort_L Omega Gamma);
[apply bucket_sort_L_permut; auto |].
clear H0 w G Gamma'; generalize dependent Gamma.
generalize dependent Omega'.
induction Omega; intros; simpl in *; constructor.
apply ok_Omega_L_permut with (O2:=a::Omega'++Omega) in H.
destruct H; intro; elim H; rewrite Mem_app_or_eq; left; auto.
permut_simpl.
apply IHOmega. apply ok_Omega_L_permut with (O1:=Omega'++a::Omega);
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
apply ok_Hyb_permut_any0 with (G1:= flat_map snd_ (bucket_sort_L Omega Gamma)).
apply flat_map_snd_permut; apply bucket_sort_L_permut; auto.
clear H1 Gamma' G.
generalize dependent U;
generalize dependent w;
generalize dependent Gamma.
induction Omega.
intros; simpl in *; constructor.
intro Gamma;
generalize dependent a;
generalize dependent Omega.
induction Gamma; intros; simpl in *.
rew_app; apply IHOmega; destruct H; auto.
destruct a; destruct p; destruct H; destruct H0; case_if; rew_app.
constructor; auto; rewrite bucket_sort_L_smaller; auto.
destruct (Mem_dec var Omega v); [apply eq_var_dec | |].
apply ok_Hyb_permut_any0 with (G1 := (v0,t)::gather_keys_L a0 Gamma ++
                               flat_map snd_ (bucket_sort_L Omega Gamma)).
permut_simpl; rew_app; rewrite flat_map_bucket_sort_L; auto.
constructor; auto; apply IHGamma.
rewrite bucket_sort_L_smaller; auto; apply IHGamma; intros. apply IHOmega; auto.
split; auto. auto. apply ok_Gamma_L_weakening_used with (u:=v0); auto.
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

(* Term conversion *)

Inductive L_to_Hyb_term: vwo -> te_L -> te_Hyb -> Prop :=
| hyp_L_Hyb:
    forall v w, L_to_Hyb_term w (hyp_L v) (hyp_Hyb v)
| lam_L_Hyb:
    forall M N A w,
      L_to_Hyb_term w M N ->
      L_to_Hyb_term w (lam_L A M) (lam_Hyb A N)
| appl_L_Hyb:
    forall M1 M2 N1 N2 w,
      L_to_Hyb_term w M1 N1 ->
      L_to_Hyb_term w M2 N2 ->
      L_to_Hyb_term w (appl_L M1 M2) (appl_Hyb N1 N2)
| box_L_Hyb:
    forall L M N w,
      (forall w0, w0 \notin L -> L_to_Hyb_term (fwo w0) M N) ->
      L_to_Hyb_term w (box_L M) (box_Hyb N)
| unbox_L_Hyb:
    forall M N w,
      L_to_Hyb_term w M N ->
      L_to_Hyb_term w (unbox_L M) (unbox_fetch_Hyb w N)
| here_L_Hyb:
    forall M N w,
      L_to_Hyb_term w M N ->
      L_to_Hyb_term w (here_L M) (get_here_Hyb w N)
| letd_L_Hyb:
    forall M1 M2 N1 N2 w,
      L_to_Hyb_term w M1 N1 ->
      L_to_Hyb_term w M2 N2 ->
      L_to_Hyb_term w (letd_L M1 M2) (letdia_get_Hyb w N1 N2)
| fetch_L_Hyb:
    forall M N w w',
      L_to_Hyb_term w M N ->
      L_to_Hyb_term w' (fetch_L w M) (box_Hyb (unbox_fetch_Hyb w N))
| get_L_Hyb:
    forall M N w w',
      L_to_Hyb_term w M N ->
      L_to_Hyb_term w'
        (get_L w M)
        (letdia_get_Hyb w N (get_here_Hyb (bwo 0)
                            (hyp_Hyb (bte 0))))
.

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
intros; symmetry; rewrite surjective_pairing; symmetry.
rewrite split_at_Hyb_fst_same; auto.
symmetry in H0; rewrite surjective_pairing in H0; symmetry in H0;
inversion H0; subst.
rewrite split_at_Hyb_snd_cons with (Delta:=Gamma_Hyb); auto.
Qed.

Lemma L_to_Hyb_term_subst_t:
forall M N w C1 C2 v,
  L_to_Hyb_term w M N ->
  (forall w0, L_to_Hyb_term w0 C1 C2) ->
  L_to_Hyb_term w (subst_t_L C1 v M) (subst_t_Hyb C2 v N).
induction M; intros; inversion H; subst; simpl in *; try case_if;
auto; try constructor; auto.
apply box_L_Hyb with (L:=L); intros; apply IHM; auto.
unfold shift_vte in *; destruct v0; [inversion H1 | discriminate].
Qed.

Lemma L_to_Hyb_term_subst_w:
forall M N w w' w1 w2,
  L_to_Hyb_term (fwo w) M N ->
  w' = (if (eq_vwo_dec (fwo w) w2) then w1 else (fwo w)) ->
  L_to_Hyb_term w' (subst_w_L M w1 w2) (subst_w_Hyb w1 w2 N).
Admitted.

Lemma L_to_Hyb_typing:
forall Omega_L Gamma_L M_L A w_L G_Hyb Gamma_Hyb M_Hyb,
  L_to_Hyb_ctx Omega_L Gamma_L w_L = (G_Hyb, Some (w_L, Gamma_Hyb)) ->
  L_to_Hyb_term (fwo w_L) M_L M_Hyb ->
  Omega_L; Gamma_L |- M_L ::: A @ w_L ->
  G_Hyb |= (w_L, Gamma_Hyb) |- M_Hyb ::: A.
unfold L_to_Hyb_ctx; intros;
generalize dependent G_Hyb;
generalize dependent Gamma_Hyb;
generalize dependent M_Hyb;
induction H1; intros; inversion H0; subst; simpl in *.
(* hyp *)
constructor;
[apply ok_L_to_Hyb_ctx_ok_Hyb with (Omega:=Omega) (Gamma:=Gamma) (w:=w)| ];
auto; eapply Mem_L_to_Hyb_ctx; eauto.
(* lam *)
apply t_lam_Hyb with (L:=L);
[eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto | intros]; unfold open_t_Hyb in *;
unfold open_t_L in *; apply H with (x:=v'); auto.
apply L_to_Hyb_term_subst_t; simpl; auto.
intros; constructor.
destruct Ok;
apply split_at_Hyb_cons; auto.
(* appl *)
apply t_appl_Hyb with (A:=A);
[eapply ok_L_to_Hyb_ctx_ok_Hyb |
 apply IHtypes_L1 | apply IHtypes_L2]; eauto.
(* box *)
apply t_box_Hyb with (L:=L0 \u L \u from_list (map fst_ Gamma)).
eapply ok_Bg_Hyb_PPermut_Hyb with (y:= (w, Gamma_Hyb) :: G_Hyb);
[PPermut_Hyb_simpl | eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto].
intros; unfold open_w_L in *; unfold open_w_Hyb in *.
assert (G_Hyb & (w, Gamma_Hyb) ~=~ bucket_sort_L Omega Gamma).
apply permut_PPermut_Hyb;
rewrite bucket_sort_L_permut with (w:=w) (Gamma':=Gamma_Hyb) (G:=G_Hyb);
[permut_simpl | unfold L_to_Hyb_ctx; auto].
rewrite H3. apply H; auto.
apply L_to_Hyb_term_subst_w with (w:=w'); simpl; auto; case_if; auto.
case_if.
assert (gather_keys_L w' Gamma = nil).
  skip. (* ! From w' freshness*)
rewrite H5; auto.
(* unbox *)
apply t_unbox_Hyb; auto;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
(* fetch *)
Focus 2.
(* here *)
apply t_here_Hyb; auto;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
(* get *)
Focus 3.
(* letd *)
apply t_letdia_Hyb with (L_w:=Lw) (L_t:=Lt) (A:=A); auto.
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
intros; unfold open_t_Hyb in *; unfold open_t_L in *;
unfold open_w_Hyb in *; unfold open_w_L in *.
apply H with (t:=v') (w':=w'); auto.
apply  L_to_Hyb_term_subst_t.
apply L_to_Hyb_term_subst_w with (w:=w).
auto. case_if; auto. intros; constructor.
repeat case_if.






Close Scope labeled_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.