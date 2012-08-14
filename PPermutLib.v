Require Export Shared.
Require Export PermutLib.

Require Import Setoid.
Require Export LibListSorted.
Require Export LibList.

Open Scope permut_scope.

Inductive PPermut: list Context_LF -> list Context_LF -> Prop :=
| PPermut_nil: PPermut nil nil
| PPermut_skip: forall G G' w Gamma Gamma', 
    Gamma *=* Gamma' ->
    PPermut G G' ->
    PPermut ((w, Gamma)::G) ((w,Gamma')::G')
| PPermut_swap: forall G w w' Gamma0 Gamma0' Gamma1 Gamma1',
    Gamma0 *=* Gamma1 ->
    Gamma0' *=* Gamma1' ->
    PPermut ((w, Gamma0) :: (w', Gamma0') :: G)
                ((w', Gamma1') :: (w, Gamma1) :: G)
| PPermut_trans: forall G G' G'',
    PPermut G G' -> PPermut G' G'' -> PPermut G G''.
Hint Constructors PPermut.

Notation "G ~=~ G'" := (PPermut G G') (at level 70) : permut_scope. 

Lemma PPermut_reflexive:
  Reflexive PPermut.
unfold Reflexive; intros;
induction x;
  [ | destruct a]; 
  eauto.
Qed. 

Lemma PPermut_symmetric:
  Symmetric PPermut.
unfold Symmetric; intros;
induction H; eauto.
  apply PPermut_trans with (G':=(w, Gamma')::G); eauto;
  apply PPermut_skip;
  [ apply permut_sym | 
    apply PPermut_reflexive];
  auto.
  apply PPermut_swap; apply permut_sym; assumption.
Qed.

Lemma PPermut_transitive:
  Transitive PPermut.
exact PPermut_trans.
Qed.  
Hint Resolve PPermut_reflexive PPermut_symmetric.

Theorem PPermut'oid: Setoid_Theory _ PPermut.
  split.
  exact PPermut_reflexive.
  exact PPermut_symmetric.
  exact PPermut_transitive.
Qed.

Add Setoid (list Context_LF) PPermut PPermut'oid as PPermutoid.

Lemma test1:
  forall G, PPermut G G.
auto.
Qed.

Add Morphism (@cons Context_LF) : PPermut_cons.
intro y; destruct y; auto.
Qed.
Hint Resolve PPermut_cons.

Lemma test2:
  forall G G' w Gamma, PPermut G G' -> PPermut ((w, Gamma)::G) ((w, Gamma) :: G').
auto.
Qed.

Lemma test3:
  forall G G' w Gamma, PPermut G G' -> PPermut ((w, Gamma)::G') ((w, Gamma) :: G).
intros;
apply PPermutoid;
auto.
Qed.

Lemma PPermut_app_tail:
forall G G' G0,
  G ~=~ G' ->
  G ++ G0 ~=~ G' ++ G0.
intros; induction H; simpl; rew_app; auto;
econstructor; eauto.
Qed.

Lemma PPermut_app_head:
forall G0 G G',
  G ~=~ G' ->
  G0 ++ G ~=~ G0 ++ G'.
intros; induction G0; simpl; rew_app; auto.
Qed.
Hint Resolve PPermut_app_tail PPermut_app_head.

Add Morphism (@append Context_LF) : PPermut_app.
intros; induction H; simpl in *; rew_app; auto.
transitivity ((w, Gamma0) :: (w', Gamma0') :: G ++ y0); auto.
transitivity (G' ++ y0); auto.
Qed.
Hint Resolve PPermut_app.

Lemma test4:
forall G G' G'' G0 G1 Ctx,
  G ~=~ G' ->
  G0 ~=~ G1 ->
  G ++ Ctx :: G'' ++ G0 ~=~ G' ++ Ctx :: G'' ++ G1.
auto.
Qed.

Theorem PPermut_app_comm:
forall G1 G2,
  G1 ++ G2 ~=~ G2 ++ G1.
induction G1; intros; simpl; rew_app;
[ auto |
 induction G2]; simpl in *;
[ rewrite app_nil_r; auto |
  destruct a; destruct a0]; 
transitivity ((v,l) :: (v0, l0) :: G2 ++ G1);
[ constructor; auto; apply IHG1 |
  transitivity ((v0, l0) :: (v, l) :: G2 ++ G1); auto];
rew_app; constructor; auto;
transitivity ((v,l) :: G1 ++ G2); auto.
Qed.
Hint Resolve PPermut_app_comm.

Lemma test5:
forall G G' G'' G0 G1,
  G ~=~ G' ->
  G0 ~=~ G1 ->
  G0 ++ G ++ G'' ~=~ G' ++ G1 ++ G''.
intros; transitivity (G ++ G0 ++ G'');
repeat rewrite <- app_assoc; auto.
Qed.

Theorem PPermut_cons_app:
forall G2 G1 G3 a,
  G1 ~=~ G2 ++ G3 ->
  a :: G1 ~=~ G2 ++ a :: G3.
induction G2; intros; simpl in *; rew_app; auto;
transitivity (a0 :: a :: G2 ++ G3); auto;
transitivity (a :: a0 :: G2 ++ G3); auto;
destruct a; destruct a0; auto.
Qed.
Hint Resolve PPermut_cons_app.

Theorem PPermut_middle:
forall G1 G2 a,
  a :: G1 ++ G2 ~=~ G1 ++ a :: G2.
auto.
Qed.

Lemma PPermut_nil_impl:
forall L,
  nil ~=~ L -> L = nil.
intros; remember (@nil Context_LF) as L' in H;
induction H; intros;
discriminate || auto.
Qed.

Lemma PPermut_nil_contr:
forall L a,
  ~ (PPermut nil (a::L)).
induction L; intros; intro;
apply PPermut_nil_impl in H; discriminate.
Qed.

Hint Resolve PPermut_nil_impl PPermut_nil_contr.

Lemma PPermut_last_simpl:
forall L L' a, 
  L ~=~ L' ->
  L & a ~=~ L' & a.
intros; apply PPermut_app_tail; auto.
Qed.

Lemma PPermut_last:
forall L L' w t t',
  t *=* t' ->
  L ~=~ L' ->
  L & (w, t) ~=~ L' & (w, t').
induction L; destruct L'; intros; simpl;
auto.
Qed.

Hint Resolve PPermut_last_simpl PPermut_last.

Lemma PPermut_mid_last_app:
forall G' G G0,
  G ++ G' ~=~ G0 ->
  forall a,
    G & a ++ G' ~=~ G0 & a.
intros; rew_app;
transitivity (a:: nil ++ G0);
[ simpl; apply PPermut_symmetric in H; apply PPermut_symmetric | ];
auto.
Qed.
Hint Resolve PPermut_mid_last_app.

Lemma PPermut_cons_last_same:
forall L a,
  a :: L ~=~ L & a.
induction L; intros;
[ | rew_app]; auto;
transitivity (a :: a0 :: L); [destruct a0; destruct a | ]; auto.
Qed.

Lemma PPermut_cons_last:
forall L L' a,
  L ~=~ L' ->
  a :: L ~=~ L' & a.
intros; rewrite H; apply PPermut_cons_last_same.
Qed.
Hint Resolve PPermut_cons_last_same PPermut_cons_last.

Lemma PPermut_swap2:
forall C C' G,
  C :: G & C' ~=~ G & C & C'.
Admitted.
Hint Resolve PPermut_swap2.

(* FIXME: Admitted *)
Lemma PPermut_last_rev_simpl:
forall G G' a,
  G & a ~=~ G' & a ->
  G ~=~ G'.
Admitted.


(* FIXME: Admitted *)
Lemma PPermut_last_rev:
forall G G' w Gamma Gamma',
  Gamma *=* Gamma' ->
  G & (w, Gamma) ~=~ G' & (w, Gamma') ->
  G ~=~ G'.
Admitted.

(* FIXME: Admitted *)
Lemma PPermut_split_neq:
forall G G' w w' Gamma Gamma',
  G & (w, Gamma) ~=~ G' & (w', Gamma') ->
  ~Gamma *=* Gamma' \/ w <> w' ->
  exists GH, exists GT, G = GH & (w', Gamma') ++ GT.
Admitted.

(* FIXME: Admitted *)
Lemma PPermut_middle_last:
forall G G' C,
  G ++ G' & C ~=~ G ++ C :: G'.
Admitted.
Hint Resolve PPermut_middle_last.

(* FIXME: Admitted *)
(* FIXME: Too specialized *)
Lemma PPermut_specialized1:
forall G G' C C',
  G ++ C :: G' & C' ~=~ G ++ G' ++ C' :: C :: nil.
Admitted.

(* FIXME: Admitted *)
(* FIXME: Too specialized *)
Lemma PPermut_specialized2:
forall GH GT G Gamma Gamma' Gamma'',
  GH ++ Gamma :: GT & Gamma' ~=~ G & Gamma ->
  GH ++ GT ++ Gamma'' :: Gamma' :: nil ~=~ G & Gamma''.
Admitted.

(* FIXME: Admitted *)
(* FIXME: Too specialized *)
Lemma PPermut_specialized3:
forall G G' C C',
  G ++ G' ++ C :: C' :: nil ~=~ G ++ C :: G' & C'.
Admitted.

(* FIXME: Admitted *)
(* FIXME: Too specialized *)
Lemma PPermut_specialized4:
forall G GH GT Gamma Gamma0 Gamma'0,
  GH ++ Gamma :: GT & Gamma'0 ~=~ G & Gamma ->
  G ++ Gamma0 :: Gamma :: nil ~=~ GH ++ GT ++ Gamma0 :: Gamma'0 :: Gamma :: nil.
Admitted.

(* FIXME: Admitted *)
(* FIXME: Too specialized *)
Lemma PPermut_specialized5:
forall G G' C C' C'',
  G ++ C :: G' ++ C' :: C'' :: nil ~=~ (G ++ G' ++ C' :: C'' :: nil) & C.
Admitted.

(* FIXME: Admitted *)
(* FIXME: Too specialized *)
Lemma PPermut_specialized6:
forall GH GT C0 C'' C'0,
  GH ++ GT ++ C'0 :: C'' :: C0 :: nil ~=~ GH ++ GT ++ C0 :: C'0 :: C'' :: nil.
Admitted.

Lemma PPermut_swap_inner:
forall G G' C C',
  C :: G ++ C' :: G' ~=~ C' :: G ++ G' & C.
Admitted.

Lemma PPermut_swap_inner2:
forall G G' C C',
  C :: G ++ G' & C' ~=~ C' :: G ++ G' & C.
Admitted.

Lemma PPermut_swap3:
forall C C' G,
  C :: G & C' ~=~ C' :: G & C.
Admitted.

Lemma PPermut_swap4:
forall C G' G,
  G ++ G' & C ~=~ G & C ++ G'.
Admitted.


Hint Resolve PPermut_swap_inner.
Hint Resolve PPermut_swap_inner2.
Hint Resolve PPermut_swap3 PPermut_swap4.

Hint Resolve PPermut_specialized1 PPermut_specialized2 
             PPermut_specialized3 PPermut_specialized4
             PPermut_specialized5 PPermut_specialized6.

Close Scope permut_scope.

