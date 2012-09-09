Require Import Setoid.
Require Import LibTactics.

Require Export Shared.
Require Export PermutLib.

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
Hint Resolve PPermut_nil PPermut_skip PPermut_swap.
Hint Constructors PPermut : ppermut_rew.

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
induction H; eauto with ppermut_rew.
  apply PPermut_trans with (G':=(w, Gamma')::G); eauto with ppermut_rew;
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
  forall G G' w Gamma,
  PPermut G G' -> PPermut ((w, Gamma)::G) ((w, Gamma) :: G').
auto.
Qed.

Lemma test3:
  forall G G' w Gamma,
    PPermut G G' -> PPermut ((w, Gamma)::G') ((w, Gamma) :: G).
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


(*** Automation **)
(* Based on permutation tactics from tlc's LibListSorted *)

Lemma PPermut_get_1 : forall l1 l2,
  PPermut (l1 ++ l2) (l1 ++ l2).
auto.
Qed.

Lemma PPermut_get_2 : forall l1 l2 l3,
  PPermut (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
intros;
assert (l1 ++ l2 ~=~ l2 ++ l1) as H by auto;
transitivity ((l1 ++ l2) ++ l3); [ | rewrite H ]; rew_app; auto.
Qed.

Lemma PPermut_get_3 : forall l1 l2 l3 l4,
  PPermut (l1 ++ l2 ++ l3 ++ l4) (l2 ++ l3 ++ l1 ++ l4).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_get_2.
Qed.

Lemma PPermut_get_4 : forall l1 l2 l3 l4 l5,
  PPermut (l1 ++ l2 ++ l3 ++ l4 ++ l5)
         (l2 ++ l3 ++ l4 ++ l1 ++ l5).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_get_3.
Qed.

Lemma PPermut_get_5 : forall l1 l2 l3 l4 l5 l6,
  PPermut (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6)
         (l2 ++ l3 ++ l4 ++ l5 ++ l1 ++ l6).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_get_4.
Qed.

Lemma PPermut_get_6 : forall l1 l2 l3 l4 l5 l6 l7,
  PPermut (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7)
         (l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l1 ++ l7).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_get_5.
Qed.

Lemma PPermut_tactic_setup : forall l1 l2,
  PPermut (nil ++ l1 ++ nil) (l2 ++ nil) -> PPermut l1 l2.
intros; rew_app in *; auto.
Qed.

Lemma PPermut_tactic_keep : forall l1 l2 l3 l4,
  PPermut ((l1 ++ l2) ++ l3) l4 ->
  PPermut (l1 ++ (l2 ++ l3)) l4.
intros; rew_app in *; auto.
Qed.

Lemma PPermut_tactic_simpl : forall l1 l2 l3 l4,
  PPermut (l1 ++ l3) l4 ->
  PPermut (l1 ++ (l2 ++ l3)) (l2 ++ l4).
intros; rewrite <- H; apply PPermut_get_2.
Qed.

Lemma PPermut_tactic_trans : forall l1 l2 l3,
  PPermut l3 l2 -> PPermut l1 l3 -> PPermut l1 l2.
intros; eauto with ppermut_rew.
Qed.

Hint Rewrite app_assoc app_nil_l app_nil_r : ppermut_rew.

Ltac PPermut_lemma_get n :=
  match nat_from_number n with
  | 1 => constr:(PPermut_get_1)
  | 2 => constr:(PPermut_get_2)
  | 3 => constr:(PPermut_get_3)
  | 4 => constr:(PPermut_get_4)
  | 5 => constr:(PPermut_get_5)
  end.

Ltac PPermut_isolate_cons :=
  do 20 try (* todo : repeat *)
    match goal with |- context [?x::?l] =>
      match l with
      | nil => fail 1
      | _ => rewrite <- (@app_cons_one _ x l)
      end
    end.

Ltac PPermut_simpl_prepare :=
   autorewrite with ppermut_rew;
   PPermut_isolate_cons;
   autorewrite with ppermut_rew;
   apply PPermut_tactic_setup;
   repeat rewrite app_assoc.

Ltac PPermut_index_of l lcontainer :=
  match constr:(lcontainer) with
  | l ++ _ => constr:(1)
  | _ ++ l ++ _ => constr:(2)
  | _ ++ _ ++ l ++ _ => constr:(3)
  | _ ++ _ ++ _ ++ l ++ _ => constr:(4)
  | _ ++ _ ++ _ ++ _ ++ l ++ _ => constr:(5)
  | _ ++ _ ++ _ ++ _ ++ _ ++ l ++ _ => constr:(6)
  | _ => constr:(0) (* not found *)
  end.

Ltac PPermut_simpl_once :=
  match goal with
  | |- PPermut (_ ++ nil) _ => fail 1
  | |- PPermut (_ ++ (?l ++ _)) ?l' =>
     match PPermut_index_of l l' with
     | 0 => apply PPermut_tactic_keep
     | ?n => let F := PPermut_lemma_get n in
            eapply PPermut_tactic_trans;
            [ apply F
            | apply PPermut_tactic_simpl ]
     end
  end.

Ltac PPermut_simpl :=
  PPermut_simpl_prepare;
  repeat PPermut_simpl_once;
  autorewrite with ppermut_rew;
  try apply PPermut_reflexive;
  auto.


(*** Other required lemmas - not covered by PPermut_simpl tactic ***)

Lemma PPermut_Mem:
forall G G' w X,
  G ~=~ G' ->
  Mem (w, X) G ->
  exists X', X' *=* X /\ Mem (w, X') G'.
Admitted.

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

Lemma PPermut_last_rev_simpl:
forall G G' a,
  G & a ~=~ G' & a ->
  G ~=~ G'.
Admitted. (* !!! *)

Lemma PPermut_last_rev:
forall G G' w Gamma Gamma',
  Gamma *=* Gamma' ->
  G & (w, Gamma) ~=~ G' & (w, Gamma') ->
  G ~=~ G'.
intros;
assert (G & (w, Gamma) ~=~ G' & (w, Gamma)) by eauto with ppermut_rew;
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); auto.
Qed.

(* FIXME: Check which variant is really required! *)
Lemma PPermut_split_neq:
forall G G' w w' Gamma Gamma',
  G & (w, Gamma) ~=~ G' & (w', Gamma') ->
  ~Gamma *=* Gamma' \/ w <> w' ->
  exists Gamma0, exists GH, exists GT,
    Gamma0 *=* Gamma' ->
    G = GH & (w', Gamma0) ++ GT.
Admitted. (* !!! *)

Lemma PPermut_specialized_case:
forall GH GT G Gamma Gamma' Gamma'',
  GH ++ Gamma :: GT & Gamma' ~=~ G & Gamma ->
  GH ++ GT ++ Gamma'' :: Gamma' :: nil ~=~ G & Gamma''.
intros; PPermut_simpl; apply PPermut_last_rev_simpl with (a:=Gamma);
rew_app; rewrite <- H; PPermut_simpl.
Qed.

Lemma PPermut_specialized_case2:
forall G GH GT Gamma Gamma0 Gamma'0,
  GH ++ Gamma :: GT & Gamma'0 ~=~ G & Gamma ->
  G ++ Gamma0 :: Gamma :: nil ~=~ GH ++ GT ++ Gamma0 :: Gamma'0 :: Gamma :: nil.
intros; PPermut_simpl; apply PPermut_last_rev_simpl with (a:=Gamma);
rew_app; rewrite <- H; PPermut_simpl.
Qed.

Hint Resolve PPermut_specialized_case PPermut_specialized_case2 : ppermut_rew.

Close Scope permut_scope.
