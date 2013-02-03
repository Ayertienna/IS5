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
unfold L_to_Hyb_ctx. intros;
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


(* Term conversion *)

(* FIXME: Move this to Hybrid/Hyb_Syntax *)
(* ?? *)
Fixpoint shift_term_Hyb (M: te_Hyb) :=
match M with
| hyp_Hyb v => M
| lam_Hyb t M => lam_Hyb t (shift_term_Hyb M)
| appl_Hyb M1 M2 => appl_Hyb (shift_term_Hyb M1) (shift_term_Hyb M2)
| box_Hyb M => box_Hyb (shift_term_Hyb M)
| unbox_fetch_Hyb w M => unbox_fetch_Hyb (shift_vwo w) (shift_term_Hyb M)
| get_here_Hyb w M => get_here_Hyb (shift_vwo w) (shift_term_Hyb M)
| letdia_get_Hyb w M N => letdia_get_Hyb (shift_vwo w) (shift_term_Hyb M)
                                         (shift_term_Hyb N)
end.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma shift_vwo_shift_term_Hyb:
forall M w0 w1,
  {{shift_vwo w0 // shift_vwo w1}} (shift_term_Hyb M) =
  shift_term_Hyb ({{w0 // w1}} M).
induction M; intros; simpl in *; auto;
try (rewrite IHM; eauto);
try (rewrite IHM1; try rewrite IHM2; eauto);
repeat case_if; auto; try destruct v; try destruct w1; simpl in *;
inversion H; subst; elim H0; auto.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma lc_w_n_shift_term_Sn_Hyb:
forall N n,
  lc_w_n_Hyb (S n) (shift_term_Hyb N) ->
  lc_w_n_Hyb n N.
induction N; intros; inversion H; subst; simpl in *; unfold shift_vwo in *;
try (destruct v; inversion H0; subst);
constructor; auto; omega.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma subst_t_Hyb_shift_term_Hyb:
forall N C v,
  lc_w_Hyb C ->
  subst_t_Hyb (shift_term_Hyb C) v (shift_term_Hyb N) =
  shift_term_Hyb (subst_t_Hyb C v N).
induction N; intros; simpl; try case_if; simpl;
try (rewrite IHN; eauto);
try (rewrite IHN1; try rewrite IHN2; auto); auto.
Qed.

(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma subst_w_Hyb_comm2:
forall M w w' m n
  (Neq: m <> n),
  {{fwo w'//bwo m }}({{fwo w//bwo n}}M) =
  {{fwo w//bwo n}}({{fwo w'//bwo m}}M).
induction M; intros; simpl;
repeat case_if; subst; simpl; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
auto.
Qed.

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
      L_to_Hyb_term (shift_vwo w) M2 N2 ->
      L_to_Hyb_term w (letd_L M1 M2) (letdia_get_Hyb w N1 N2)
| fetch_L_Hyb:
    forall L M N w w',
      (forall w0, w0 \notin L -> L_to_Hyb_term w M
                                   (N ^w^ (fwo w0)))->
      L_to_Hyb_term w' (fetch_L w M)
                       (box_Hyb (unbox_fetch_Hyb (shift_vwo w)
                                                 (shift_term_Hyb N)))
| get_L_Hyb:
    forall M N w w',
      L_to_Hyb_term w M N ->
      L_to_Hyb_term w'
        (get_L w M)
        (letdia_get_Hyb w N
                        (get_here_Hyb (bwo 0)
                                      (hyp_Hyb (bte 0))))
.

Lemma L_to_Hyb_term_subst_w:
forall M N w,
  L_to_Hyb_term w M N ->
  forall w0 n w',
    (w' = if eq_vwo_dec w (bwo n) then (fwo w0) else w) ->
    L_to_Hyb_term w' (subst_w_L M (fwo w0) (bwo n))
                     (subst_w_Hyb (fwo w0) (bwo n) N).
intros M N w H; induction H; intros; simpl in *; repeat case_if;
simpl in *; try subst; eauto using L_to_Hyb_term.
constructor; eapply IHL_to_Hyb_term; eauto; case_if; auto.
constructor; eapply IHL_to_Hyb_term; eauto; case_if; auto.
constructor; [eapply IHL_to_Hyb_term1 | eapply IHL_to_Hyb_term2];
try case_if; auto.
constructor; [eapply IHL_to_Hyb_term1 | eapply IHL_to_Hyb_term2];
try case_if; auto.
apply box_L_Hyb with (L:=L \u \{w0});
intros; apply H0 with (w0:=w1); eauto; case_if; eauto; simpl in *;
inversion H2; subst; repeat rewrite notin_union in H1;
destruct H1 as (a, (b, c)); rewrite notin_singleton in c; elim c; auto.
apply box_L_Hyb with (L:=L \u \{w0});
intros; apply H0 with (w0:=w1); eauto; case_if; eauto; simpl in *;
inversion H3; subst; repeat rewrite notin_union in H1;
destruct H1 as (a, (b, c)); rewrite notin_singleton in c; elim c; auto.
constructor; eapply IHL_to_Hyb_term; eauto; case_if; auto.
constructor; eapply IHL_to_Hyb_term; eauto; case_if; auto.
constructor; eapply IHL_to_Hyb_term; eauto; case_if; auto.
constructor; eapply IHL_to_Hyb_term; eauto; case_if; auto.
constructor; [eapply IHL_to_Hyb_term1 | eapply IHL_to_Hyb_term2];
try case_if; auto.
constructor; [eapply IHL_to_Hyb_term1 | eapply IHL_to_Hyb_term2];
try case_if; auto; destruct w; simpl in *; inversion H1;
subst; elim H2; auto.
replace (bwo (S n)) with (shift_vwo (bwo n)) by (simpl; auto).
replace (fwo w0) with (shift_vwo (fwo w0)) by (simpl; auto).
rewrite shift_vwo_shift_term_Hyb. simpl.
apply fetch_L_Hyb with (L:=L \u \{w0});
intros; unfold open_w_Hyb in *.
destruct n; simpl in *.
assert ({{fwo w1 // bwo 0}}({{fwo w0 // bwo 0}}N) = {{fwo w0 // bwo 0}}N).
skip.
rewrite H3. eapply H0.
rewrite <- subst_w_Hyb_comm2; eauto.
eapply H0; try case_if; auto.
apply fetch_L_Hyb with (L:=L \u \{w0} \u \{w1});
intros; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; eauto;
eapply H0; try case_if; auto.
elim H2; auto.
elim H2; auto.
destruct w; simpl in *; inversion H3; subst; contradiction.
destruct w; simpl in *; inversion H3; subst; contradiction.
apply fetch_L_Hyb with (L:=L \u \{w0} \u \{w1});
intros; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; eauto;
eapply H0; try case_if; auto.
apply fetch_L_Hyb with (L:=L \u \{w0} \u \{w1});
intros; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; eauto;
eapply H0; try case_if; auto.
constructor; eapply IHL_to_Hyb_term; case_if; eauto.
constructor; eapply IHL_to_Hyb_term; case_if; eauto.
constructor; eapply IHL_to_Hyb_term; case_if; eauto.
constructor; eapply IHL_to_Hyb_term; case_if; eauto.
Qed.
(*
intros M N w H; induction H; intros; case_if; subst; simpl in *; repeat case_if;
try (constructor; eapply IHL_to_Hyb_term; case_if; auto);
try (constructor; [eapply IHL_to_Hyb_term1 | eapply IHL_to_Hyb_term2];
     case_if; auto).
apply box_L_Hyb with (L:=L \u var_from_vwo w0 \u var_from_vwo w1);
intros; apply H0 with (w0:=w2); eauto; case_if; eauto;
destruct w1; destruct w0; simpl in *;
inversion H2; subst; repeat rewrite notin_union in H1;
destruct H1 as (a, (b, c)); rewrite notin_singleton in c; elim c; auto.
apply box_L_Hyb with (L:=L \u var_from_vwo w0 \u var_from_vwo w1);
intros; apply H0 with (w0:=w2); eauto; case_if; eauto;
destruct w1; destruct w0; simpl in *;
inversion H3; subst; repeat rewrite notin_union in H1;
destruct H1 as (a, (b, c)); rewrite notin_singleton in c; elim c; auto.
destruct w1; destruct w; simpl in *; inversion H3; subst; try (elim H1; auto).
unfold open_w_Hyb in *.
(*
rewrite shift_vwo_shift_term_Hyb; constructor; eapply IHL_to_Hyb_term;
case_if; eauto.
destruct w; destruct w1; simpl in *; inversion H1; subst; elim H0; auto.
rewrite shift_vwo_shift_term_Hyb; constructor; eapply IHL_to_Hyb_term;
case_if; eauto.
rewrite shift_vwo_shift_term_Hyb; constructor; eapply IHL_to_Hyb_term;
case_if; eauto.
destruct w; destruct w1; simpl in *; inversion H2; subst; elim H0; auto.
rewrite shift_vwo_shift_term_Hyb; constructor; eapply IHL_to_Hyb_term;
case_if; eauto.
destruct w1; simpl in *; inversion H0.
destruct w1; simpl in *; inversion H1.
destruct w1; simpl in *; inversion H0.
destruct w1; simpl in *; inversion H2.
Qed.
*) *)

Lemma L_to_Hyb_term_subst_t:
forall M N w C1 C2 v,
  L_to_Hyb_term w M N -> lc_w_Hyb C2 ->
  (forall w0, L_to_Hyb_term w0 C1 C2) ->
  L_to_Hyb_term w (subst_t_L C1 v M) (subst_t_Hyb C2 v N).
induction M; intros; inversion H; subst; simpl in *; try case_if;
auto; try constructor; auto.
apply box_L_Hyb with (L:=L); intros; apply IHM; auto.
unfold shift_vte in *; destruct v0; [inversion H2 | discriminate].
apply fetch_L_Hyb with (L:=L); intros;
unfold open_w_Hyb in *; simpl in *.
rewrite <- subst_Hyb_order_irrelevant_bound.
eapply IHM; auto.
auto.
Qed.

(* FIXME: Move this to Labeled/Lists/L_Substitution *)
Lemma lc_w_subst_t_L:
forall N M v n,
  lc_w_n_L n M ->
  lc_w_n_L n N ->
  lc_w_n_L n (subst_t_L M v N).
induction N; intros; inversion H0; subst; simpl in *; try case_if;
auto; constructor; try eapply IHN; eauto. apply closed_w_succ_L; auto.
eapply IHN2; [apply closed_w_succ_L | ]; auto.
Qed.

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

(* FIXME: Move this to Labeled/Lists/L_Semantics *)
Lemma types_L_Mem_Omega:
forall M Omega Gamma A w,
  Omega; Gamma |- M ::: A @ w ->
  Mem w Omega.
intros; induction H; eauto;
assert (exists x, x \notin L) as H0 by apply Fresh; destruct H0 as (x);
apply H with (x:=x); auto.
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

(* FIXME: do we really need all the 'locally closed' assumptions? *)
Lemma L_to_Hyb_typing:
forall Omega_L Gamma_L M_L A w_L G_Hyb Gamma_Hyb M_Hyb,
  L_to_Hyb_ctx Omega_L Gamma_L w_L = (G_Hyb, Some (w_L, Gamma_Hyb)) ->
  L_to_Hyb_term (fwo w_L) M_L M_Hyb ->
  lc_w_L M_L -> lc_w_Hyb M_Hyb ->
  Omega_L; Gamma_L |- M_L ::: A @ w_L ->
  G_Hyb |= (w_L, Gamma_Hyb) |- M_Hyb ::: A.
unfold L_to_Hyb_ctx; intros;
generalize dependent G_Hyb;
generalize dependent Gamma_Hyb;
generalize dependent M_Hyb;
induction H3; intros; inversion H0; subst; simpl in *;
inversion H1; inversion H2; subst.
(* hyp *)
constructor;
[apply ok_L_to_Hyb_ctx_ok_Hyb with (Omega:=Omega) (Gamma:=Gamma) (w:=w)| ];
auto; eapply Mem_L_to_Hyb_ctx; eauto.
(* lam *)
apply t_lam_Hyb with (L:=L);
[eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto | intros]; unfold open_t_Hyb in *;
unfold open_t_L in *; apply H with (x:=v'); auto.
apply lc_w_subst_t_L; [constructor | ]; auto.
apply L_to_Hyb_term_subst_t; simpl; auto.
constructor. intros; constructor.
apply lc_w_subst_t_Hyb; [constructor | ]; auto.
destruct Ok; apply split_at_Hyb_cons; auto.
(* appl *)
apply t_appl_Hyb with (A:=A);
[eapply ok_L_to_Hyb_ctx_ok_Hyb |
 apply IHtypes_L1 | apply IHtypes_L2]; eauto.
(* box *)
apply t_box_Hyb with (L:=L \u L0 \u
                           from_list (map fst Gamma)).
assert (G_Hyb & (w, Gamma_Hyb) ~=~ (w, Gamma_Hyb) :: G_Hyb) as HP
  by PPermut_Hyb_simpl; rewrite HP;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
intros; unfold open_w_L in *; unfold open_w_Hyb in *.
assert ( G_Hyb & (w, Gamma_Hyb) ~=~ bucket_sort_L Omega Gamma).
  apply permut_PPermut_Hyb.
  symmetry; rewrite bucket_sort_L_permut with
            (w:=w) (Gamma':=Gamma_Hyb) (G:=G_Hyb); [permut_simpl | ]; auto.
rewrite H5.
eapply H; eauto. apply lc_w_subst_L; auto.
apply L_to_Hyb_term_subst_w with (w:=fwo w').
apply H6; eauto. case_if; auto.
apply lc_w_subst_Hyb; auto.
case_if; destruct Ok.
rewrite gather_keys_L_fresh; [|apply notin_Mem]; eauto.
(* unbox *)
apply t_unbox_Hyb; auto;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
(* fetch *)
apply t_box_Hyb with (L:=L \u used_w_vars_Hyb ((w', Gamma_Hyb) :: G_Hyb)).
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb) :: G_Hyb)
  by PPermut_Hyb_simpl; rewrite H4;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
intros; unfold open_w_L in *; unfold open_w_Hyb in *; simpl;
case_if.
destruct (eq_var_dec w w'); subst.
(* w = w' *)
apply t_unbox_fetch_Hyb with (G:=G_Hyb) (Gamma:=Gamma_Hyb); auto.
assert ((w', Gamma_Hyb) :: G_Hyb & (w'0, nil) ~=~
        (w'0, nil) :: (w', Gamma_Hyb) :: G_Hyb) by PPermut_Hyb_simpl;
rewrite H7; apply ok_Bg_Hyb_fresh_wo; [eapply ok_L_to_Hyb_ctx_ok_Hyb | ]; eauto.
inversion H11; subst.
assert (G_Hyb & (w'0, nil) ~=~ nil & (w'0, nil) ++ G_Hyb) by PPermut_Hyb_simpl.
rewrite H7; apply GlobalWeakening_Hyb; rew_app.
eapply IHtypes_L; auto.
(*apply lc_w_n_shift_term_Sn_Hyb in H10.
rewrite lc_w_shift_term_Hyb; auto;
inversion H0; subst. apply H13; auto.
rewrite closed_subst_w_Hyb_bound with (n:=0); auto. *)
apply lc_w_subst_Hyb; auto.
assert ((w', Gamma_Hyb) :: (w'0, nil) :: G_Hyb ~=~
        (w'0, nil) :: (w', Gamma_Hyb) :: G_Hyb) by PPermut_Hyb_simpl;
rewrite H9. apply ok_Bg_Hyb_fresh_wo; auto;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
(* w <> w' *)
assert (exists G0, exists Gamma0,
          split_at_Hyb (bucket_sort_L Omega Gamma) w = (G0, Some (w, Gamma0))).
  exists (fst (split_at_Hyb (bucket_sort_L Omega Gamma) w)).
  assert (exists Gamma1, snd (split_at_Hyb (bucket_sort_L Omega Gamma) w) =
                 Some (w, Gamma1)).
  apply L_to_Hyb_ctx_Mem_Some.
  apply types_L_Mem_Omega in H3; auto.
  destruct H7; exists x; rewrite <- H7; apply surjective_pairing.
destruct H7 as (G0, (Gamma0, H7)).
assert ((w, Gamma0) :: G0 *=* (w', Gamma_Hyb) :: G_Hyb).
  transitivity (bucket_sort_L Omega Gamma); [symmetry | ];
  apply bucket_sort_L_permut; eauto.
apply t_unbox_fetch_Hyb with (G:=G0) (Gamma:=Gamma0).
assert ((w, Gamma0) :: G0 & (w'0, nil) ~=~
        (w'0, nil) :: (w, Gamma0) :: G0) by PPermut_Hyb_simpl.
rewrite H10; apply ok_Bg_Hyb_fresh_wo; [eapply ok_L_to_Hyb_ctx_ok_Hyb | ];
eauto. rewrite PPermut_Hyb_used_w with (y:=(w', Gamma_Hyb)::G_Hyb); auto;
apply permut_PPermut_Hyb; auto.
inversion H11; subst.
assert (G0 & (w'0, nil) ~=~ nil & (w'0, nil) ++ G0) by PPermut_Hyb_simpl.
rewrite H10; apply GlobalWeakening_Hyb; rew_app.
eapply IHtypes_L; auto.
(*apply lc_w_n_shift_term_Sn_Hyb in H13;
rewrite lc_w_shift_term_Hyb; auto;
rewrite closed_subst_w_Hyb_bound with (n:=0); auto.*)
apply lc_w_subst_Hyb; auto.
assert ((w, Gamma0) :: (w'0, nil) :: G0 ~=~
        (w'0, nil) :: (w, Gamma0) :: G0) by PPermut_Hyb_simpl;
rewrite H12. apply ok_Bg_Hyb_fresh_wo; auto.
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
rewrite PPermut_Hyb_used_w with (y:=(w', Gamma_Hyb)::G_Hyb); auto.
apply permut_PPermut_Hyb; auto.
apply permut_PPermut_Hyb;
transitivity ((w, Gamma0)::G0); [| rewrite H9]; permut_simpl.
(* here *)
apply t_here_Hyb; auto;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
(* get *)
destruct (eq_var_dec w w'); subst.
(* w = w' *)
apply t_letdia_Hyb with (A:=A) (L_w:=used_w_vars_Hyb (G_Hyb & (w', Gamma_Hyb)))
                               (L_t:=used_t_vars_Hyb (G_Hyb & (w', Gamma_Hyb))).
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
eapply IHtypes_L; auto.
intros; unfold open_t_Hyb; unfold open_w_Hyb; simpl; repeat case_if.
apply t_get_here_Hyb with (G:=G_Hyb) (Gamma:=(v',A)::nil).
apply ok_Bg_Hyb_fresh_wo_te; auto.
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb) :: G_Hyb)
  by PPermut_Hyb_simpl; rewrite H7;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
constructor.
apply ok_Bg_Hyb_fresh_wo_te; auto.
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb) :: G_Hyb)
  by PPermut_Hyb_simpl; rewrite H7;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
apply Mem_here.
PPermut_Hyb_simpl.
(* w <> w' *)
assert (exists G0, exists Gamma0,
          split_at_Hyb (bucket_sort_L Omega Gamma) w = (G0, Some (w, Gamma0))).
  exists (fst (split_at_Hyb (bucket_sort_L Omega Gamma) w)).
  assert (exists Gamma1, snd (split_at_Hyb (bucket_sort_L Omega Gamma) w) =
                 Some (w, Gamma1)).
  apply L_to_Hyb_ctx_Mem_Some.
  apply types_L_Mem_Omega in H3; auto.
  destruct H7; exists x; rewrite <- H7; apply surjective_pairing.
destruct H7 as (G0, (Gamma0, H7)).
assert ((w, Gamma0) :: G0 *=* (w', Gamma_Hyb) :: G_Hyb).
  transitivity (bucket_sort_L Omega Gamma); [symmetry | ];
  apply bucket_sort_L_permut; eauto.
apply t_unbox_fetch_Hyb with (G:=G0) (Gamma:=Gamma0).
assert ((w, Gamma0) :: G0 & (w'0, nil) ~=~
        (w'0, nil) :: (w, Gamma0) :: G0) by PPermut_Hyb_simpl.
rewrite H10; apply ok_Bg_Hyb_fresh_wo; [eapply ok_L_to_Hyb_ctx_ok_Hyb | ];
eauto. rewrite PPermut_Hyb_used_w with (y:=(w', Gamma_Hyb)::G_Hyb); auto;
apply permut_PPermut_Hyb; auto.
inversion H11; subst.
assert (G0 & (w'0, nil) ~=~ nil & (w'0, nil) ++ G0) by PPermut_Hyb_simpl.
rewrite H10; apply GlobalWeakening_Hyb; rew_app.
eapply IHtypes_L; auto.
apply lc_w_n_shift_term_Sn_Hyb in H13;
rewrite lc_w_shift_term_Hyb; auto;
rewrite closed_subst_w_Hyb_bound with (n:=0); auto.
apply lc_w_subst_Hyb; auto.
assert ((w, Gamma0) :: (w'0, nil) :: G0 ~=~
        (w'0, nil) :: (w, Gamma0) :: G0) by PPermut_Hyb_simpl;
rewrite H12. apply ok_Bg_Hyb_fresh_wo; auto.
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
rewrite PPermut_Hyb_used_w with (y:=(w', Gamma_Hyb)::G_Hyb); auto.
apply permut_PPermut_Hyb; auto.
apply permut_PPermut_Hyb;
transitivity ((w, Gamma0)::G0); [| rewrite H9]; permut_simpl.

(* letd *)
apply t_letdia_Hyb with (L_w:=Lw \u from_list Omega \u from_list (map fst Gamma)
                              \u used_w_vars_Hyb ((w, Gamma_Hyb) :: G_Hyb))
                          (L_t:=Lt \u used_t_vars_Hyb ((w, Gamma_Hyb) :: G_Hyb))
                          (A:=A); auto;
[eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto | intros];
unfold open_w_L in *; unfold open_w_Hyb in *;
unfold open_t_L in *; unfold open_t_Hyb in *.
clear IHtypes_L HT2.
assert (lc_w_L
           (subst_t_L (hyp_L (fte v')) (bte 0)
                      (subst_w_L N (fwo w') (bwo 0)))).
  apply lc_w_subst_t_L; [ constructor | apply lc_w_subst_L]; auto.
assert (G_Hyb & (w, Gamma_Hyb) ~=~ bucket_sort_L Omega Gamma).
  apply permut_PPermut_Hyb.
  symmetry; rewrite bucket_sort_L_permut with
            (w:=w) (Gamma':=Gamma_Hyb) (G:=G_Hyb); [permut_simpl | ]; auto.
eapply H; eauto. eauto. eauto.
apply L_to_Hyb_term_subst_t; [ | constructor | intros; constructor ];
apply L_to_Hyb_term_subst_w with (w:=fwo w); auto; case_if; auto.
apply lc_w_subst_t_Hyb; [constructor | apply lc_w_subst_Hyb]; auto.
repeat case_if.
simpl in *; repeat rewrite notin_union in H6; destruct H6; destruct H13;
destruct H14; destruct H16; rewrite notin_singleton in H16; elim H16; auto.
rewrite bucket_sort_L_smaller; [| apply notin_Mem]; eauto;
rewrite gather_keys_L_fresh; [| apply notin_Mem]; eauto;
symmetry in H4; rewrite surjective_pairing in H4; inversion H4; subst;
rewrite H18; auto.
Qed
              .

Lemma L_to_Hyb_steps:
forall M N w M',
  L_to_Hyb_term w M N ->
  steps_L (M, w) (M', w) ->
  exists N', steps_Hyb (N, w) (N', w) /\ L_to_Hyb_term w M' N'.
Admitted.

Lemma L_to_Hyb_term_left_total:
forall M w,
  exists N, L_to_Hyb_term w M N.
Admitted. (* problem for box *)

Close Scope labeled_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.