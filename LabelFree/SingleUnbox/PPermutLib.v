Add LoadPath "../..".
Require Import Setoid.
Require Export LibTactics.
Require Export PermutLib.
Require Export Shared.

Open Scope permut_scope.

Inductive PPermut_LF: list ctx_LF -> list ctx_LF -> Prop :=
| PPermut_LF_nil: PPermut_LF nil nil
| PPermut_LF_skip: forall G G' A A',
  A *=* A' -> PPermut_LF G G' -> PPermut_LF (A::G) (A'::G')
| PPermut_LF_swap: forall G A A' B B',
  A *=* A' -> B *=* B' -> PPermut_LF (A::B::G) (B'::A'::G)
| PPermut_LF_trans: forall G G' G'',
  PPermut_LF G G' -> PPermut_LF G' G'' -> PPermut_LF G G''
.
Hint Resolve PPermut_LF_nil PPermut_LF_skip PPermut_LF_swap.
Hint Constructors PPermut_LF : ppermut_rew.

Notation "G ~=~ G'" := (PPermut_LF G G') (at level 70).

Lemma PPermut_LF_reflexive:
  Reflexive PPermut_LF.
unfold Reflexive; intros;
induction x; eauto.
Qed.

Lemma PPermut_LF_symmetric:
  Symmetric PPermut_LF.
unfold Symmetric; intros;
induction H; eauto with ppermut_rew.
  apply PPermut_LF_trans with (G':=A'::G); eauto with ppermut_rew;
  apply PPermut_LF_skip;
  [ apply permut_sym |
    apply PPermut_LF_reflexive];
  auto.
  apply PPermut_LF_swap; apply permut_sym; assumption.
Qed.

Lemma PPermut_LF_transitive:
  Transitive PPermut_LF.
exact PPermut_LF_trans.
Qed.
Hint Resolve PPermut_LF_reflexive PPermut_LF_symmetric.

Theorem PPermut_LF'oid: Setoid_Theory _ PPermut_LF.
  split.
  exact PPermut_LF_reflexive.
  exact PPermut_LF_symmetric.
  exact PPermut_LF_transitive.
Qed.

Add Setoid (list ctx_LF) PPermut_LF PPermut_LF'oid as PPermut_LFoid.

Add Morphism (@cons ctx_LF) : PPermut_LF_cons.
intro y; destruct y; auto.
Qed.
Hint Resolve PPermut_LF_cons.

Lemma PPermut_LF_app_tail:
forall G G' G0,
  G ~=~ G' ->
  G ++ G0 ~=~ G' ++ G0.
intros; induction H; simpl; rew_app; auto;
econstructor; eauto.
Qed.

Lemma PPermut_LF_app_head:
forall G0 G G',
  G ~=~ G' ->
  G0 ++ G ~=~ G0 ++ G'.
intros; induction G0; simpl; rew_app; auto.
Qed.
Hint Resolve PPermut_LF_app_tail PPermut_LF_app_head.

Add Morphism (@append ctx_LF) : PPermut_LF_app.
intros; induction H; simpl in *; rew_app; auto.
transitivity (A'::B'::G ++ y0); eauto.
transitivity (G' ++ y0); auto.
Qed.
Hint Resolve PPermut_LF_app.

Theorem PPermut_LF_app_comm:
forall G1 G2,
  G1 ++ G2 ~=~ G2 ++ G1.
induction G1; intros; simpl; rew_app;
[ auto |
 induction G2]; simpl in *;
[ rewrite app_nil_r; auto | ].
transitivity (a :: a0 :: G2 ++ G1);
[ constructor; auto; apply IHG1 |
  transitivity (a0 :: a :: G2 ++ G1); auto];
constructor; auto;
transitivity (a :: G1 ++ G2); auto.
Qed.
Hint Resolve PPermut_LF_app_comm.


(*** Automation **)
(* Based on permutation tactics from tlc's LibListSorted *)

Lemma PPermut_LF_get_1 : forall l1 l2,
  PPermut_LF (l1 ++ l2) (l1 ++ l2).
auto.
Qed.

Lemma PPermut_LF_get_2 : forall l1 l2 l3,
  PPermut_LF (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
intros;
assert (l1 ++ l2 ~=~ l2 ++ l1) as H by auto;
transitivity ((l1 ++ l2) ++ l3); [ | rewrite H ]; rew_app; auto.
Qed.

Lemma PPermut_LF_get_3 : forall l1 l2 l3 l4,
  PPermut_LF (l1 ++ l2 ++ l3 ++ l4) (l2 ++ l3 ++ l1 ++ l4).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_LF_get_2.
Qed.

Lemma PPermut_LF_get_4 : forall l1 l2 l3 l4 l5,
  PPermut_LF (l1 ++ l2 ++ l3 ++ l4 ++ l5)
         (l2 ++ l3 ++ l4 ++ l1 ++ l5).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_LF_get_3.
Qed.

Lemma PPermut_LF_get_5 : forall l1 l2 l3 l4 l5 l6,
  PPermut_LF (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6)
         (l2 ++ l3 ++ l4 ++ l5 ++ l1 ++ l6).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_LF_get_4.
Qed.

Lemma PPermut_LF_get_6 : forall l1 l2 l3 l4 l5 l6 l7,
  PPermut_LF (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7)
         (l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l1 ++ l7).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_LF_get_5.
Qed.

Lemma PPermut_LF_tactic_setup : forall l1 l2,
  PPermut_LF (nil ++ l1 ++ nil) (l2 ++ nil) -> PPermut_LF l1 l2.
intros; rew_app in *; auto.
Qed.

Lemma PPermut_LF_tactic_keep : forall l1 l2 l3 l4,
  PPermut_LF ((l1 ++ l2) ++ l3) l4 ->
  PPermut_LF (l1 ++ (l2 ++ l3)) l4.
intros; rew_app in *; auto.
Qed.

Lemma PPermut_LF_tactic_simpl : forall l1 l2 l3 l4,
  PPermut_LF (l1 ++ l3) l4 ->
  PPermut_LF (l1 ++ (l2 ++ l3)) (l2 ++ l4).
intros; rewrite <- H; apply PPermut_LF_get_2.
Qed.

Lemma PPermut_LF_tactic_trans : forall l1 l2 l3,
  PPermut_LF l3 l2 -> PPermut_LF l1 l3 -> PPermut_LF l1 l2.
intros; eauto with ppermut_rew.
Qed.

Hint Rewrite app_assoc app_nil_l app_nil_r : ppermut_rew.

Ltac PPermut_LF_lemma_get n :=
  match nat_from_number n with
  | 1 => constr:(PPermut_LF_get_1)
  | 2 => constr:(PPermut_LF_get_2)
  | 3 => constr:(PPermut_LF_get_3)
  | 4 => constr:(PPermut_LF_get_4)
  | 5 => constr:(PPermut_LF_get_5)
  end.

Ltac PPermut_LF_isolate_cons :=
  do 20 try (* todo : repeat *)
    match goal with |- context [?x::?l] =>
      match l with
      | nil => fail 1
      | _ => rewrite <- (@app_cons_one _ x l)
      end
    end.

Ltac PPermut_LF_simpl_prepare :=
   autorewrite with ppermut_rew;
   PPermut_LF_isolate_cons;
   autorewrite with ppermut_rew;
   apply PPermut_LF_tactic_setup;
   repeat rewrite app_assoc.

Ltac PPermut_LF_index_of l lcontainer :=
  match constr:(lcontainer) with
  | l ++ _ => constr:(1)
  | _ ++ l ++ _ => constr:(2)
  | _ ++ _ ++ l ++ _ => constr:(3)
  | _ ++ _ ++ _ ++ l ++ _ => constr:(4)
  | _ ++ _ ++ _ ++ _ ++ l ++ _ => constr:(5)
  | _ ++ _ ++ _ ++ _ ++ _ ++ l ++ _ => constr:(6)
  | _ => constr:(0) (* not found *)
  end.

Ltac PPermut_LF_simpl_once :=
  match goal with
  | |- PPermut_LF (_ ++ nil) _ => fail 1
  | |- PPermut_LF (_ ++ (?l ++ _)) ?l' =>
     match PPermut_LF_index_of l l' with
     | 0 => apply PPermut_LF_tactic_keep
     | ?n => let F := PPermut_LF_lemma_get n in
            eapply PPermut_LF_tactic_trans;
            [ apply F
            | apply PPermut_LF_tactic_simpl ]
     end
  end.

Ltac PPermut_LF_simpl :=
  PPermut_LF_simpl_prepare;
  repeat PPermut_LF_simpl_once;
  autorewrite with ppermut_rew;
  try apply PPermut_LF_reflexive;
  auto.


(*** Other lemmas ***)
(* Note:
   Some are covered by PPermut_LF_simpl tactic, but we want to use them in auto! *)

Lemma PPermut_LF_Mem:
forall G G' X,
  G ~=~ G' ->
  Mem X G ->
  exists X', X' *=* X /\ Mem X' G'.
intros; generalize dependent X; induction H; intros.
rewrite Mem_nil_eq in H0; contradiction.
rewrite Mem_cons_eq in H1; destruct H1.
subst; exists A'; split; [ symmetry | apply Mem_here]; auto.
apply IHPPermut_LF in H1; destruct H1 as (Gamma''); exists Gamma'';
destruct H1; split; auto; rewrite Mem_cons_eq; right; auto.
repeat rewrite Mem_cons_eq in H1; destruct H1.
subst; exists A'; split; [ symmetry | rewrite Mem_cons_eq];
auto; right; apply Mem_here.
destruct H1.
subst; exists B'; split; [ symmetry | rewrite Mem_cons_eq];
auto.
exists X; split; auto; repeat rewrite Mem_cons_eq; right; right; auto.
apply IHPPermut_LF1 in H1; destruct H1 as (X'); destruct H1.
apply IHPPermut_LF2 in H2; destruct H2 as (X''); destruct H2;
exists X''; split; auto; transitivity X'; auto.
Qed.

Lemma PPermut_LF_nil_impl:
forall L,
  nil ~=~ L -> L = nil.
intros; remember (@nil ctx_LF) as L' in H;
induction H; intros;
discriminate || auto.
Qed.

Lemma PPermut_LF_nil_contr:
forall L a,
  ~ (PPermut_LF nil (a::L)).
induction L; intros; intro;
apply PPermut_LF_nil_impl in H; discriminate.
Qed.

Hint Resolve PPermut_LF_nil_impl PPermut_LF_nil_contr.

(* Based on Sorting/Permutation/Permutation_ind_bis *)
Theorem PPermut_LF_ind_bis :
 forall P : list ctx_LF -> list ctx_LF -> Prop,
   P nil nil ->
   (forall x y l l', l ~=~ l' -> P l l' ->
     x *=* y -> P (x :: l) (y :: l')) ->
   (forall x x' y y' l l', l ~=~ l' -> P l l' -> x *=* x' -> y *=* y' ->
     P (y :: x :: l) (x' :: y' :: l')) ->
   (forall l l' l'', l ~=~ l' -> P l l' -> l' ~=~ l'' -> P l' l'' -> P l l'') ->
   forall l l', l ~=~ l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans;
  intros; induction H; auto.
  apply Htrans with (B :: A :: G); auto.
    apply Hswap; auto; induction G; auto.
    apply Hskip; auto; apply Hskip; auto; induction G; auto;
    destruct a; apply Hskip; auto.
  eauto.
Qed.

Lemma PPermut_LF_app_rev:
forall G G' H H' a a',
  a *=* a' ->
  G & a ++ G' ~=~ H & a' ++ H' ->
  G ++ G' ~=~ H ++ H'.
Proof.
  set (P l l' :=
         forall a a' l1 l2 l3 l4, a *=* a' ->
         l=l1 & a ++ l2 -> l'=l3 & a' ++l4 -> (l1++l2) ~=~ (l3++l4)).
  cut (forall l l', l ~=~ l' -> P l l').
  intros; apply (H _ _ H2 a a'); auto.
  intros; apply (PPermut_LF_ind_bis P); unfold P; clear P;
    try clear H l l'; simpl; auto.
  (* nil *)
  intros; destruct l1; simpl in *; discriminate.
  (* skip *)
  intros x y l l' H IH; intros.
  destruct l1; destruct l3; rew_app in *;
  inversion H2; inversion H3; subst; auto.
    rewrite H; PPermut_LF_simpl; constructor; [transitivity a |] ; auto;
      symmetry; auto.
    rewrite <- H; PPermut_LF_simpl; constructor; auto; transitivity a';
      [ | symmetry]; auto.
  constructor; auto.
  apply (IH a a' l1 l2 l5 l4); rew_app; auto.
  (* swap *)
  intros x x' y y' l l' Hp IH; intros.
  destruct l1; destruct l2; rew_app in *; subst;
  inversion H2; subst; auto; try rewrite Hp; rew_app;
  PPermut_LF_simpl; destruct l3; destruct l4; rew_app in *; subst;
  inversion H3; subst; auto.
    constructor; auto; transitivity a'; auto; transitivity a; auto;
    symmetry; auto.
    constructor; auto; destruct l3; rew_app in *; inversion H6; subst; auto;
      PPermut_LF_simpl; constructor; auto; transitivity a; auto; symmetry; auto.
    constructor; auto; destruct l3; rew_app in *; inversion H6; subst; auto;
      PPermut_LF_simpl; constructor; auto; transitivity a; auto; symmetry; auto.
    constructor; auto; destruct l1; rew_app in *; inversion H6; subst; auto;
      PPermut_LF_simpl; rewrite <- Hp; PPermut_LF_simpl; constructor; auto;
      transitivity a'; auto; symmetry; auto.
  destruct l1; destruct l3; rew_app in *; inversion H6; inversion H7; subst.
      constructor; auto; transitivity a'; auto; transitivity a; auto;
        symmetry; auto.
       apply PPermut_LF_nil_impl in Hp; destruct l3; rew_app in *; discriminate.
       symmetry in Hp; apply PPermut_LF_nil_impl in Hp; destruct l4; rew_app in *;
         discriminate.
       clear H2 H3 H6 H7.
       transitivity (l3 :: l2 :: l4).
         constructor; [ | constructor]; auto.
         PPermut_LF_simpl.
       replace l4 with (l4 ++ nil) by (rew_app; auto);
       replace l5 with (l5 ++ nil) by (rew_app; auto);
       apply IH with (a0:=a) (a'0:=a'); auto;
         rew_app; auto.
  destruct l1; destruct l3; rew_app in *; inversion H6; inversion H7; subst;
    auto.
       apply PPermut_LF_nil_impl in Hp; discriminate.
       apply PPermut_LF_nil_impl in Hp; destruct l3; rew_app in *; discriminate.
       rewrite <- Hp; PPermut_LF_simpl; rew_app; apply PPermut_LF_swap;
       [ transitivity a' | ]; auto; symmetry; auto;
       clear H7 H3 H2 H6;
       transitivity (l2::l3::l6); auto; PPermut_LF_simpl; rew_app;
       replace l6 with (l6 ++ nil) by (rew_app; auto);
       apply IH with (a0:=a) (a'0:=a'); auto;
         rew_app; auto.
    transitivity (l1::l0::l6); [PPermut_LF_simpl|];
    constructor; auto; constructor; auto;
    replace l6 with (l6++nil) by (rew_app; auto);
    apply IH with (a0:=a)(a'0:=a'); eauto;
    rew_app; auto.
  rewrite <- Hp; symmetry; destruct l1; rew_app in *;
    inversion H6; subst; auto; PPermut_LF_simpl; constructor; auto.
    symmetry; auto.
    constructor; auto; transitivity a'; [ | symmetry]; auto.
  destruct l6; rew_app in *; inversion H7; subst.
    symmetry in Hp; apply PPermut_LF_nil_impl in Hp; subst; inversion H6; subst;
      destruct l1; rew_app in *; inversion H6; subst; destruct l1; rew_app in *;
      discriminate.
    transitivity (l4 ::l1 ++ l2 :: l5); PPermut_LF_simpl; rew_app.
    destruct l1; rew_app in *; inversion H6; subst.
      rewrite Hp; PPermut_LF_simpl; constructor; auto; transitivity a; auto;
      symmetry; auto.
      constructor; auto; replace l6 with (l6 ++ nil) by (rew_app; auto);
      apply IH with (a0:=a) (a'0:=a'); auto; rew_app; auto.
  destruct l1; destruct l6; rew_app in *; inversion H6;
  inversion H7; subst.
    constructor; auto; transitivity a; auto; transitivity a'; auto;
    symmetry; auto.
    transitivity (l1:: l2 :: l5).
      constructor; auto.
      PPermut_LF_simpl. rew_app; rewrite Hp; PPermut_LF_simpl;
      constructor; auto; transitivity a; auto; symmetry; auto.
    transitivity (l1::l4::l7).
      PPermut_LF_simpl; rew_app; rewrite <- Hp; PPermut_LF_simpl; constructor;
        auto; transitivity a'; auto; symmetry; auto.
      constructor; auto.
    transitivity (l6 :: l3 :: l8 ++ l2 :: l5).
      constructor; auto; constructor; auto.
      PPermut_LF_simpl. rew_app.
    apply IH with (a0:=a) (a'0:=a'); rew_app; auto.
  (* trans *)
  intros. destruct (PPermut_LF_Mem l l' a) as (a'', (H6a, H6b)); auto.
    subst; rewrite Mem_app_or_eq; left; rewrite Mem_app_or_eq; right;
      apply Mem_here.
  destruct (Mem_split ctx_LF l' a'') as (l'1, (l'2, H6)); auto.
  transitivity (l'1 ++ l'2).
    apply H0 with (a:=a) (a':=a''); [ symmetry | | ]; auto.
    apply H2 with (a:=a'') (a':=a').
      transitivity a; auto; symmetry; auto.
      auto.
      auto.
Qed.

Lemma PPermut_LF_last_rev_simpl:
forall G G' a,
  G & a ~=~ G' & a ->
  G ~=~ G'.
intros. replace G with (G ++ nil);
replace G' with (G'++nil).
destruct a; eapply PPermut_LF_app_rev; rew_app; eauto.
rew_app; auto.
rew_app; auto.
rew_app; auto.
Qed.

Lemma PPermut_LF_last_rev:
forall G G' Gamma Gamma',
  Gamma *=* Gamma' ->
  G & Gamma ~=~ G' & Gamma' ->
  G ~=~ G'.
intros;
assert (G & Gamma ~=~ G' & Gamma) by eauto with ppermut_rew;
apply PPermut_LF_last_rev_simpl with (a:=Gamma); auto.
Qed.

Lemma PPermut_LF_split_head:
forall G G' Gamma,
  Gamma :: G ~=~ G' ->
  exists Gamma' hd tl,
    Gamma *=* Gamma' /\ G' = hd & Gamma' ++ tl.
intros.
apply PPermut_LF_Mem with (X:=Gamma) in H.
destruct H as (Gamma'); destruct H.
exists Gamma'.
assert (exists hd, exists tl, G' = hd & Gamma' ++ tl) by
  (eapply Mem_split; auto).
destruct H1 as (hd, (tl, H1));
exists hd; exists tl; split; [symmetry | ]; auto.
apply Mem_here.
Qed.

Lemma PPermut_LF_split_neq:
forall G G' Gamma Gamma',
  G & Gamma ~=~ G' & Gamma' ->
  ~Gamma *=* Gamma' ->
  exists Gamma0, exists GH, exists GT,
    Gamma0 *=* Gamma' /\
    G = GH & Gamma0 ++ GT.
intros.
assert (Gamma ::G  ~=~ (G' & Gamma')) by
  (transitivity (G & Gamma); auto; PPermut_LF_simpl).
assert (Gamma :: G ~=~ Gamma' :: G') by
  (transitivity (G' & Gamma'); auto; PPermut_LF_simpl).
symmetry in H2;
apply PPermut_LF_split_head in H2; destruct H2 as (Gamma'',(GH, (GT, (Ha, Hb)))).
destruct GH; rew_app in *.
inversion Hb; subst. elim H0; symmetry; auto.
inversion Hb; subst.
exists Gamma''; exists GH; exists GT; split;
[symmetry | rew_app]; auto.
Qed.

Lemma PPermut_LF_swap2:
forall C C' G,
  C :: G & C' ~=~ G & C & C'.
intros; PPermut_LF_simpl.
Qed.
Hint Resolve PPermut_LF_swap2.

Lemma PPermut_LF_middle_last:
forall G G' C,
  G ++ G' & C ~=~ G ++ C :: G'.
intros; PPermut_LF_simpl.
Qed.
Hint Resolve PPermut_LF_middle_last.

Lemma PPermut_LF_specialized1:
forall G G' C C',
  G ++ C :: G' & C' ~=~ G ++ G' ++ C' :: C :: nil.
intros; PPermut_LF_simpl.
Qed.

Lemma PPermut_LF_specialized2:
forall GH GT G Gamma Gamma' Gamma'',
  GH ++ Gamma :: GT & Gamma' ~=~ G & Gamma ->
  GH ++ GT ++ Gamma'' :: Gamma' :: nil ~=~ G & Gamma''.
intros; PPermut_LF_simpl;
apply PPermut_LF_last_rev_simpl with (a:=Gamma);
rewrite <- H; PPermut_LF_simpl.
Qed.

Lemma PPermut_LF_specialized3:
forall G G' C C',
  G ++ G' ++ C :: C' :: nil ~=~ G ++ C :: G' & C'.
intros; PPermut_LF_simpl.
Qed.

Lemma PPermut_LF_specialized4:
forall G GH GT Gamma Gamma0 Gamma'0,
  GH ++ Gamma :: GT & Gamma'0 ~=~ G & Gamma ->
  G ++ Gamma0 :: Gamma :: nil ~=~ GH ++ GT ++ Gamma0 :: Gamma'0 :: Gamma :: nil.
intros; PPermut_LF_simpl;
apply PPermut_LF_last_rev_simpl with (a:=Gamma); rewrite <- H;
PPermut_LF_simpl.
Qed.

Lemma PPermut_LF_specialized5:
forall G G' C C' C'',
  G ++ C :: G' ++ C' :: C'' :: nil ~=~ (G ++ G' ++ C' :: C'' :: nil) & C.
intros; PPermut_LF_simpl.
Qed.

Lemma PPermut_LF_specialized6:
forall GH GT C0 C'' C'0,
  GH ++ GT ++ C'0 :: C'' :: C0 :: nil ~=~ GH ++ GT ++ C0 :: C'0 :: C'' :: nil.
intros; PPermut_LF_simpl.
Qed.

Lemma PPermut_LF_swap_inner:
forall G G' C C',
  C :: G ++ C' :: G' ~=~ C' :: G ++ G' & C.
intros; PPermut_LF_simpl.
Qed.

Lemma PPermut_LF_swap_inner2:
forall G G' C C',
  C :: G ++ G' & C' ~=~ C' :: G ++ G' & C.
intros; PPermut_LF_simpl.
Qed.

Lemma PPermut_LF_swap3:
forall C C' G,
  C :: G & C' ~=~ C' :: G & C.
intros; PPermut_LF_simpl.
Qed.

Lemma PPermut_LF_swap4:
forall C G' G,
  G ++ G' & C ~=~ G & C ++ G'.
intros; PPermut_LF_simpl.
Qed.

Hint Resolve PPermut_LF_swap_inner.
Hint Resolve PPermut_LF_swap_inner2.
Hint Resolve PPermut_LF_swap3 PPermut_LF_swap4.

Hint Resolve PPermut_LF_specialized2 : ppermut_rew.
Hint Resolve PPermut_LF_specialized1
             PPermut_LF_specialized3 PPermut_LF_specialized4
             PPermut_LF_specialized5 PPermut_LF_specialized6.

Lemma permut_PPermut_LF:
forall G G', G *=* G' -> G ~=~ G'.
intros. induction H; auto.
transitivity y; auto.
inversion H. PPermut_LF_simpl.
Qed.

Close Scope permut_scope.
