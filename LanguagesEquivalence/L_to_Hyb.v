(*
Notes on trying to do it nicer :)

fetch w M |->_w' M ^w^ w' (or sth similar)
 - counter example:
take M0 = lam_L ([*]A) box_L (fetch_L w (hyp_L 0))
Note that {w}; nil |- M0 ::: [*]A -> [*][*]A

what will the M0's equivalent in Hyb be with such rule for fetch?

L_to_Hyb_term w M0 N0
N0 = lam_Hyb ([*]A) box_Hyb N1
where N1 is what comes as equivalent of fetch_L w (hyp_L 0).
Now, with rule for fetch stated as above, we get N1 = hyp_L 0.
That is nowhere near something that types in an empty environment.

On the other hand, M0 is the smallest program od type [*]A ---> [*][*]A.
Smallest such program in Hybrid is
lam ([*]A) (box (box (unbox_fetch w' (hyp 0))))
- exactly the equivalent of M0 when ~ "fetch w M |->_w' box (unbox_fetch w N)"

*)
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

(* Shift helpers *)

(* FIXME: Move this to Hybrid/Hyb_Syntax *)
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
Lemma lc_w_n_shift_term_Sn_Hyb:
forall N n,
  lc_w_n_Hyb (S n) (shift_term_Hyb N) <->
  lc_w_n_Hyb n N.
split; generalize dependent n; generalize dependent N.
induction N; intros; inversion H; subst; simpl in *; unfold shift_vwo in *;
try (destruct v; inversion H0; subst);
constructor; auto; omega.
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
Lemma subst_w_Hyb_shift_term_Hyb:
forall M w w',
  {{shift_vwo w // shift_vwo w'}} (shift_term_Hyb M) =
  shift_term_Hyb ({{w//w'}}M).
induction M; intros; destruct w; destruct w'; try destruct v;
simpl in *; repeat case_if;
try erewrite <- IHM;
try erewrite <- IHM1; try erewrite <- IHM2; eauto.
Qed.

Lemma test_shift_lc_w:
forall w N,
lc_w_Hyb (shift_term_Hyb N) ->
{{w // bwo 0}} (shift_term_Hyb N) = shift_term_Hyb N.
intros;
apply closed_subst_w_Hyb_bound with (n:=0); try omega; auto.
Qed.

(* Things to be moved into language definitions *)

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

(* FIXME: Move this to Labeled/Lists/L_Substitution *)
Lemma lc_w_n_L_subst_t:
forall N M v n,
lc_w_n_L n (subst_t_L M v N) ->
lc_w_n_L n N.
induction N; intros; simpl in *; try destruct v; constructor;
inversion H; subst; try eapply IHN; eauto.
Qed.

(* FIXME: Move this to Labeled/Lists/L_Substitution *)
Lemma lc_w_n_L_subst_w:
forall N w n,
lc_w_n_L n (subst_w_L N (fwo w) (bwo n)) ->
lc_w_n_L (S n) N.
induction N; intros; simpl in *; try destruct v; constructor;
inversion H; subst; try eapply IHN; eauto;
repeat case_if; inversion H0; subst; try inversion H1; subst;
try omega.
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

(* FIXME: Move this to Labeled/Lists/L_Semantics *)
Lemma types_L_lc_w_L:
forall Omega Gamma M A w,
  Omega; Gamma |- M ::: A @ w -> lc_w_L M.
intros; induction H; constructor; try apply IHHT;
unfold open_w_L in *; unfold open_t_L in *;
auto.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0; apply lc_w_n_L_subst_t in H0; auto.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0; apply lc_w_n_L_subst_w in H0; auto.
assert (exists x, x \notin Lt) by apply Fresh; destruct H1;
assert (exists x, x \notin Lw) by apply Fresh; destruct H2;
specialize H0 with x x0; apply H0 with (w':=x0) in H1; auto.
apply lc_w_n_L_subst_t in H1; apply lc_w_n_L_subst_w in H1; auto.
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

(* FIXME: Move this to Labeled/Lists/L_Substitution *)
Lemma subst_t_comm2_L:
forall M v' m n N
  (Neq: m <> n)
  (Lc: lc_t_L N),
  subst_t_L N (bte m) (subst_t_L (hyp_L (fte v')) (bte n) M) =
  subst_t_L (hyp_L (fte v')) (bte n) (subst_t_L N (bte m) M).
induction M; intros; subst; simpl;
repeat (case_if; subst; simpl); auto;
try rewrite IHM; eauto; try omega.
rewrite closed_subst_t_bound_L with (n:=0); auto; omega.
rewrite IHM1; eauto; rewrite IHM2; eauto; omega.
rewrite IHM1; eauto; rewrite IHM2; eauto; omega.
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

(* FIXME: Move this to Labeled/Lists/L_Substitution *)
Lemma subst_w_L_comm2:
forall M w w' m n
  (Neq: m <> n)
  (Neq': w <> bwo m),
  subst_w_L  (subst_w_L M w (bwo n)) (fwo w') (bwo m) =
  subst_w_L (subst_w_L M (fwo w') (bwo m)) w (bwo n).
induction M; intros; simpl; destruct w;
repeat case_if; subst; simpl; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
auto; intro nn; elim Neq'; inversion nn; subst; auto.
Qed.


(* FIXME: Move this to Hybrid/Hyb_Substitution *)
Lemma double_subst_w_Hyb_eq:
forall M w0 n m,
  subst_w_Hyb w0 (bwo n) (subst_w_Hyb (bwo n) (bwo m) M) =
  subst_w_Hyb w0 (bwo n) (subst_w_Hyb w0 (bwo m) M).
induction M; intros; simpl; repeat case_if;
try rewrite IHM;
try rewrite IHM1; try rewrite IHM2; eauto.
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
      (forall w0, w0 \notin L ->
                  L_to_Hyb_term (fwo w0) (open_w_L M (fwo w0))
                                (N^w^ (fwo w0))) ->
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
    forall Lw Lt M1 M2 N1 N2 w,
      L_to_Hyb_term w M1 N1 ->
      (forall w0, w0 \notin Lw ->
         forall v0, v0 \notin Lt ->
            L_to_Hyb_term (shift_vwo w)
                          (open_t_L (open_w_L M2 (fwo w0)) (hyp_L (fte v0)))
                          ((N2 ^w^ (fwo w0)) ^t^ (hyp_Hyb (fte v0)))) ->
      L_to_Hyb_term w (letd_L M1 M2) (letdia_get_Hyb w N1 N2)
| fetch_L_Hyb:
    forall M N w w',
      L_to_Hyb_term w M N ->
      L_to_Hyb_term w' (fetch_L w M) (box_Hyb (unbox_fetch_Hyb (shift_vwo w)
                                                         N))
| get_L_Hyb:
    forall M N w w',
      L_to_Hyb_term w M N ->
      L_to_Hyb_term w' (get_L w M)
                    (letdia_get_Hyb w N (get_here_Hyb (bwo 0)
                                                      (hyp_Hyb (bte 0))))
.

Lemma L_to_Hyb_term_subst_t:
forall M N w C1 C2 v,
  lc_t_L C1 -> lc_t_Hyb C2 ->
  L_to_Hyb_term w M N -> lc_w_Hyb C2 -> lc_w_L C1 ->
  (forall w0, L_to_Hyb_term w0 C1 C2) ->
  L_to_Hyb_term w (subst_t_L C1 v M) (subst_t_Hyb C2 v N).
intros;
generalize dependent v;
generalize dependent C1;
generalize dependent C2;
induction H1; intros; simpl in *.
(* hyp *)
case_if; auto; constructor.
(* lam *)
constructor; eauto.
(* appl *)
constructor;
[eapply IHL_to_Hyb_term1 | eapply IHL_to_Hyb_term2]; eauto.
(* box *)
apply box_L_Hyb with (L:=L); intros;
unfold open_w_L in *; unfold open_w_Hyb in *;
rewrite subst_order_irrelevant_bound_L; auto;
rewrite <- subst_Hyb_order_irrelevant_bound; auto.
(* unbox *)
constructor; eapply IHL_to_Hyb_term; eauto.
(* here *)
constructor; eapply IHL_to_Hyb_term; eauto.
(* letdia *)
apply letd_L_Hyb with (Lw:=Lw) (Lt:=Lt \u var_from_vte v).
eapply IHL_to_Hyb_term; eauto.
intros; unfold open_w_L in *; unfold open_t_L in *;
unfold open_w_Hyb in *; unfold open_t_Hyb in *.
rewrite <- subst_Hyb_order_irrelevant_bound; auto;
rewrite subst_order_irrelevant_bound_L; auto.
destruct v; simpl.
rewrite <- subst_t_comm2_L; try omega; auto;
rewrite <- subst_t_comm2_Hyb; try omega; auto.
rewrite <- subst_t_comm_L; try omega; auto;
[rewrite <- subst_t_Hyb_comm; try omega; auto | ];
rewrite notin_union in H8; destruct H8; simpl in *; eauto.
(* fetch *)
apply fetch_L_Hyb; eapply IHL_to_Hyb_term; eauto.
(* get *)
case_if; [destruct v; simpl in *; inversion H5 | ];
apply get_L_Hyb; eapply IHL_to_Hyb_term; eauto.
Qed.

Lemma L_to_Hyb_term_rename_w:
forall M N w,
  L_to_Hyb_term w M N ->
  forall w0 w1 w',
    (w' = if eq_vwo_dec w (fwo w0) then (fwo w1) else w) ->
    L_to_Hyb_term w' (subst_w_L M (fwo w1) (fwo w0))
                     (subst_w_Hyb (fwo w1) (fwo w0) N).
intros;
generalize dependent w0;
generalize dependent w1;
generalize dependent w';
induction H; intros; simpl in *.
(* hyp *)
constructor.
(* lam *)
constructor; eauto.
(* appl *)
constructor; [eapply IHL_to_Hyb_term1 | eapply IHL_to_Hyb_term2];
case_if; eauto.
(* box *)
apply box_L_Hyb with (L:=L \u \{w0}); intros;
unfold open_w_L in *; unfold open_w_Hyb in *;
rewrite <- subst_w_comm_L;
[rewrite <- subst_w_Hyb_comm; try omega; auto | ];
[eapply H0; repeat case_if; auto; inversion H3; subst | ];
rewrite notin_union in H2; destruct H2; simpl in *; eauto;
rewrite notin_singleton in H2; elim H2; auto.
(* unbox *)
rewrite <- H0; constructor;
eapply IHL_to_Hyb_term; case_if; auto.
(* here *)
rewrite <- H0; constructor;
eapply IHL_to_Hyb_term; case_if; auto.
(* letdia *)
rewrite <- H2; apply letd_L_Hyb with (Lw:=Lw \u \{w0}) (Lt:=Lt).
eapply IHL_to_Hyb_term; auto.
intros; unfold open_w_L in *; unfold open_t_L in *;
unfold open_w_Hyb in *; unfold open_t_Hyb in *.
rewrite <- subst_w_Hyb_comm; [rewrite <- subst_w_comm_L | ].
rewrite subst_Hyb_order_irrelevant_free; try (simpl; auto);
rewrite <- subst_order_irrelevant_free_L; try (simpl; auto);
eapply H1; eauto; destruct w; repeat case_if; subst; simpl in *;
auto; [inversion H5; subst; elim H6 | inversion H6; subst; elim H5]; auto.
rewrite notin_union in H3; simpl in *; destruct H3; auto.
rewrite notin_union in H3; simpl in *; destruct H3; auto.
(* fetch *)
remember (if eq_vwo_dec w (fwo w0) then fwo w1 else w) as w'1;
replace (if eq_vwo_dec (shift_vwo w) (fwo w0)
            then fwo w1
            else shift_vwo w) with (shift_vwo w'1).
constructor; auto; case_if; auto.
repeat case_if; subst; simpl; auto.
destruct w; simpl in *; try discriminate; try destruct H1; subst; elim H2; auto.
destruct w; simpl in *; try discriminate; try destruct H1; subst; elim H2; auto.
elim H1; simpl; auto.
elim H1; simpl; auto.
(* get *)
repeat case_if; apply get_L_Hyb; eapply IHL_to_Hyb_term;
case_if; auto.
Qed.

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
apply L_to_Hyb_term_subst_t; try constructor; auto.
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
intros; unfold open_w_L in *; unfold open_w_Hyb in *;
assert ( G_Hyb & (w, Gamma_Hyb) ~=~ bucket_sort_L Omega Gamma) by
  (apply permut_PPermut_Hyb;
   symmetry; rewrite bucket_sort_L_permut with
            (w:=w) (Gamma':=Gamma_Hyb) (G:=G_Hyb); [permut_simpl | ]; auto);
rewrite H3; eapply H; eauto; case_if; destruct Ok;
rewrite gather_keys_L_fresh; [|apply notin_Mem]; eauto.
(* unbox *)
apply t_unbox_Hyb; auto;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
(* fetch *)
apply t_box_Hyb with (L:=used_w_vars_Hyb ((w', Gamma_Hyb) :: G_Hyb)).
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb) :: G_Hyb) as HP
  by PPermut_Hyb_simpl; rewrite HP;
eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
intros; unfold open_w_Hyb; simpl; case_if;
destruct (eq_var_dec w w'); subst.
(* = *)
apply t_unbox_fetch_Hyb with (Gamma:=Gamma_Hyb) (G:=G_Hyb).
assert ((w', Gamma_Hyb) :: G_Hyb & (w'0, nil) ~=~
                        (w'0, nil) :: (w', Gamma_Hyb)::G_Hyb)
       by PPermut_Hyb_simpl;
rewrite H4; apply ok_Bg_Hyb_fresh_wo;
[eapply ok_L_to_Hyb_ctx_ok_Hyb | ]; eauto.
apply IHtypes_L with (M_Hyb:=N)
                             (Gamma_Hyb:=Gamma_Hyb) (G_Hyb:=G_Hyb) in H6; auto.
assert (lc_w_Hyb ( N)) by (apply types_Hyb_lc_w_Hyb in H6; auto);
rewrite closed_subst_w_Hyb_bound with (n:=0); auto;
replace G_Hyb with (G_Hyb ++ nil) in H6 by (rew_app; auto);
apply GlobalWeakening_Hyb with (Ctx':=(w'0, nil)) in H6; rew_app in *; auto.
assert ((w', Gamma_Hyb) :: G_Hyb & (w'0, nil) ~=~
                        (w'0, nil) :: (w', Gamma_Hyb)::G_Hyb)
       by PPermut_Hyb_simpl;
rewrite H5; apply ok_Bg_Hyb_fresh_wo; [eapply ok_L_to_Hyb_ctx_ok_Hyb | ]; eauto.
PPermut_Hyb_simpl.
(* <> *)
assert (exists G0, exists Gamma0,
          split_at_Hyb (bucket_sort_L Omega Gamma) w = (G0, Some (w, Gamma0))).
  exists (fst (split_at_Hyb (bucket_sort_L Omega Gamma) w)).
  assert (exists Gamma1, snd (split_at_Hyb (bucket_sort_L Omega Gamma) w) =
                 Some (w, Gamma1)).
  apply L_to_Hyb_ctx_Mem_Some.
  apply types_L_Mem_Omega in H1; auto.
  destruct H4; exists x; rewrite <- H4; apply surjective_pairing.
destruct H4 as (Gw, (Gammaw, H4)).
assert ((w, Gammaw) :: Gw *=* (w', Gamma_Hyb) :: G_Hyb).
transitivity (bucket_sort_L Omega Gamma); [symmetry | ];
  apply bucket_sort_L_permut; eauto.
assert (exists hd, exists tl, G_Hyb = hd & (w, Gammaw) ++ tl).
apply permut_neq_split with (l1:=(w, Gammaw)::Gw) (b:=(w', Gamma_Hyb)); auto.
intro nn; inversion nn; subst; elim n; auto. apply Mem_here.
destruct H7 as (hd, (tl, H7)).
apply t_unbox_fetch_Hyb with (Gamma:=Gammaw)(G:=hd++tl & (w', Gamma_Hyb)).
assert (ok_Bg_Hyb ((w'0, nil)::(w', Gamma_Hyb)::G_Hyb)) by
(eapply ok_Bg_Hyb_fresh_wo; eauto; eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto);
assert ((w'0, nil) :: (w', Gamma_Hyb) :: G_Hyb ~=~
                   (w, Gammaw) :: (hd ++ tl & (w', Gamma_Hyb)) & (w'0, nil))
by (subst; PPermut_Hyb_simpl); rewrite <- H9; auto.
apply IHtypes_L with (M_Hyb:= N)
                     (Gamma_Hyb:=Gammaw) (G_Hyb:=Gw) in H6;
auto.
assert (lc_w_Hyb ( N)) by (apply types_Hyb_lc_w_Hyb in H6; auto).
rewrite closed_subst_w_Hyb_bound with (n:=0); auto.
replace Gw with (Gw ++ nil) in H6 by (rew_app; auto).
apply GlobalWeakening_Hyb with (Ctx':=(w'0, nil)) in H6.
assert (Gw & (w'0, nil) ~=~  (hd ++ tl & (w', Gamma_Hyb)) & (w'0, nil)).
PPermut_Hyb_simpl. apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gammaw)).
transitivity ((w, Gammaw)::Gw). PPermut_Hyb_simpl.
apply permut_PPermut_Hyb in H5. rewrite H5. subst; PPermut_Hyb_simpl.
rewrite <- H9; rew_app in *; auto.
rew_app.
assert ((w, Gammaw) :: Gw & (w'0, nil) ~=~
                    (w'0, nil) :: (w', Gamma_Hyb) :: G_Hyb).
PPermut_Hyb_simpl. apply permut_PPermut_Hyb in H5; rewrite H5; auto.
rewrite H9; apply ok_Bg_Hyb_fresh_wo. eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
eauto.
subst; PPermut_Hyb_simpl.
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
  apply types_L_Mem_Omega in H1; auto.
  destruct H2; exists x; rewrite <- H2; apply surjective_pairing.
destruct H2 as (Gw, (Gammaw, H2)).
assert ((w, Gammaw) :: Gw *=* (w', Gamma_Hyb) :: G_Hyb).
transitivity (bucket_sort_L Omega Gamma); [symmetry | ];
  apply bucket_sort_L_permut; eauto.
assert (exists hd, exists tl, G_Hyb = hd & (w, Gammaw) ++ tl).
apply permut_neq_split with (l1:=(w, Gammaw)::Gw) (b:=(w', Gamma_Hyb)); auto.
intro nn; inversion nn; subst; elim n; auto. apply Mem_here.
destruct H4 as (hd, (tl, H4)).
apply t_letdia_get_Hyb with (L_w:=used_w_vars_Hyb (G_Hyb & (w', Gamma_Hyb)))
                            (L_t:=used_t_vars_Hyb (G_Hyb & (w', Gamma_Hyb)))
                            (A:=A)(G:=hd++tl)(Gamma:=Gammaw).
assert ((w, Gammaw) :: (hd ++ tl) & (w', Gamma_Hyb) ~=~
                    (w', Gamma_Hyb) :: G_Hyb)
  by (subst; PPermut_Hyb_simpl);
rewrite H5; eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
assert ((hd ++ tl) & (w', Gamma_Hyb) ~=~ Gw).
apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gammaw)).
transitivity ((w', Gamma_Hyb) :: G_Hyb).
subst; PPermut_Hyb_simpl.
apply permut_PPermut_Hyb in H3; rewrite <- H3; PPermut_Hyb_simpl.
rewrite H5; eapply IHtypes_L; auto.
intros; unfold open_w_Hyb; unfold open_t_Hyb; simpl; repeat case_if.
assert (G_Hyb & (w', Gamma_Hyb) ~=~ (w', Gamma_Hyb)::G_Hyb)
  by PPermut_Hyb_simpl.
apply t_get_here_Hyb with (G:=G_Hyb) (Gamma:=(v', A)::nil).
apply ok_Bg_Hyb_fresh_wo_te; auto;
rewrite H8; eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
constructor; [ | apply Mem_here];
apply ok_Bg_Hyb_fresh_wo_te; auto.
rewrite H8; eapply ok_L_to_Hyb_ctx_ok_Hyb; eauto.
PPermut_Hyb_simpl.
subst; PPermut_Hyb_simpl.
subst; PPermut_Hyb_simpl.
(* letd *)
apply t_letdia_Hyb with (L_w:=Lw \u Lw0 \u from_list Omega \u
                                 from_list (map fst Gamma)
                              \u used_w_vars_Hyb ((w, Gamma_Hyb) :: G_Hyb))
                          (L_t:=Lt \u Lt0 \u
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
apply H with (t:=v') (w':=w'); eauto.
repeat case_if.
simpl in *; repeat rewrite notin_union in H4; destruct H4; destruct H7;
destruct H9; destruct H10; destruct H11; rewrite notin_singleton in H11;
elim H11; auto.
rewrite bucket_sort_L_smaller; [| apply notin_Mem]; eauto;
rewrite gather_keys_L_fresh; [| apply notin_Mem]; eauto;
symmetry in H2; rewrite surjective_pairing in H2; inversion H2; subst;
rewrite H11; auto.
Qed.

Lemma L_to_Hyb_steps:
forall M N w,
  L_to_Hyb_term w M N ->
  forall M',
  step_L (M, w) (M', w) ->
  value_Hyb N \/
  exists N', step_Hyb (N, w) (N', w) /\ L_to_Hyb_term w M' N'.
Admitted.

Lemma L_to_Hyb_term_left_total:
forall M Omega Gamma A w,
  Omega; Gamma |- M ::: A @ w ->
  exists N, L_to_Hyb_term (fwo w) M N.
Admitted.

Close Scope labeled_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
