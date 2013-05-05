Add LoadPath "../..".
Require Import Setoid.
Require Export LibTactics.
Require Export HybND_Shared.
Require Export ListLib.
Require Export PermutLib.

Open Scope permut_scope.

Inductive PPermut_Hyb: list ctx_Hyb -> list ctx_Hyb -> Prop :=
| PPermut_Hyb_nil: PPermut_Hyb nil nil
| PPermut_Hyb_skip: forall G G' w Gamma Gamma',
    Gamma *=* Gamma' ->
    PPermut_Hyb G G' ->
    PPermut_Hyb ((w, Gamma)::G) ((w,Gamma')::G')
| PPermut_Hyb_swap: forall G w w' Gamma0 Gamma0' Gamma1 Gamma1',
    Gamma0 *=* Gamma1 ->
    Gamma0' *=* Gamma1' ->
    PPermut_Hyb ((w, Gamma0) :: (w', Gamma0') :: G)
                ((w', Gamma1') :: (w, Gamma1) :: G)
| PPermut_Hyb_trans: forall G G' G'',
    PPermut_Hyb G G' -> PPermut_Hyb G' G'' -> PPermut_Hyb G G''.
Hint Resolve PPermut_Hyb_nil PPermut_Hyb_skip PPermut_Hyb_swap.
Hint Constructors PPermut_Hyb : ppermut_rew.

Notation "G ~=~ G'" := (PPermut_Hyb G G') (at level 70) : permut_scope.

Lemma PPermut_Hyb_reflexive:
  Reflexive PPermut_Hyb.
unfold Reflexive; intros;
induction x; [ | destruct a]; eauto.
Qed.

Lemma PPermut_Hyb_symmetric:
  Symmetric PPermut_Hyb.
unfold Symmetric; intros;
induction H; eauto with ppermut_rew.
  apply PPermut_Hyb_trans with (G':=(w, Gamma')::G); eauto with ppermut_rew;
  apply PPermut_Hyb_skip;
  [ apply permut_sym |
    apply PPermut_Hyb_reflexive];
  auto.
  apply PPermut_Hyb_swap; apply permut_sym; assumption.
Qed.

Lemma PPermut_Hyb_transitive:
  Transitive PPermut_Hyb.
exact PPermut_Hyb_trans.
Qed.
Hint Resolve PPermut_Hyb_reflexive PPermut_Hyb_symmetric.

Theorem PPermut_Hyb'oid: Setoid_Theory _ PPermut_Hyb.
  split.
  exact PPermut_Hyb_reflexive.
  exact PPermut_Hyb_symmetric.
  exact PPermut_Hyb_transitive.
Qed.

Add Setoid (list ctx_Hyb) PPermut_Hyb PPermut_Hyb'oid as PPermut_Hyboid.

Add Morphism (@cons ctx_Hyb) : PPermut_Hyb_cons.
intro y; destruct y; auto.
Qed.
Hint Resolve PPermut_Hyb_cons.

Lemma PPermut_Hyb_app_tail:
forall G G' G0,
  G ~=~ G' ->
  G ++ G0 ~=~ G' ++ G0.
intros; induction H; simpl; rew_app; auto;
econstructor; eauto.
Qed.

Lemma PPermut_Hyb_app_head:
forall G0 G G',
  G ~=~ G' ->
  G0 ++ G ~=~ G0 ++ G'.
intros; induction G0; simpl; rew_app; auto.
Qed.
Hint Resolve PPermut_Hyb_app_tail PPermut_Hyb_app_head.

Add Morphism (@append ctx_Hyb) : PPermut_Hyb_app.
intros; induction H; simpl in *; rew_app; auto.
transitivity ((w, Gamma0) :: (w', Gamma0') :: G ++ y0); auto.
transitivity (G' ++ y0); auto.
Qed.
Hint Resolve PPermut_Hyb_app.

Theorem PPermut_Hyb_app_comm:
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
Hint Resolve PPermut_Hyb_app_comm.


(*** Automation **)
(* Based on permutation tactics from tlc's LibListSorted *)

Lemma PPermut_Hyb_get_1 : forall l1 l2,
  PPermut_Hyb (l1 ++ l2) (l1 ++ l2).
auto.
Qed.

Lemma PPermut_Hyb_get_2 : forall l1 l2 l3,
  PPermut_Hyb (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
intros;
assert (l1 ++ l2 ~=~ l2 ++ l1) as H by auto;
transitivity ((l1 ++ l2) ++ l3); [ | rewrite H ]; rew_app; auto.
Qed.

Lemma PPermut_Hyb_get_3 : forall l1 l2 l3 l4,
  PPermut_Hyb (l1 ++ l2 ++ l3 ++ l4) (l2 ++ l3 ++ l1 ++ l4).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_Hyb_get_2.
Qed.

Lemma PPermut_Hyb_get_4 : forall l1 l2 l3 l4 l5,
  PPermut_Hyb (l1 ++ l2 ++ l3 ++ l4 ++ l5)
         (l2 ++ l3 ++ l4 ++ l1 ++ l5).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_Hyb_get_3.
Qed.

Lemma PPermut_Hyb_get_5 : forall l1 l2 l3 l4 l5 l6,
  PPermut_Hyb (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6)
         (l2 ++ l3 ++ l4 ++ l5 ++ l1 ++ l6).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_Hyb_get_4.
Qed.

Lemma PPermut_Hyb_get_6 : forall l1 l2 l3 l4 l5 l6 l7,
  PPermut_Hyb (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7)
         (l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l1 ++ l7).
intros;
do 2 rewrite <- (@app_assoc _ l2); eapply PPermut_Hyb_get_5.
Qed.

Lemma PPermut_Hyb_tactic_setup : forall l1 l2,
  PPermut_Hyb (nil ++ l1 ++ nil) (l2 ++ nil) -> PPermut_Hyb l1 l2.
intros; rew_app in *; auto.
Qed.

Lemma PPermut_Hyb_tactic_keep : forall l1 l2 l3 l4,
  PPermut_Hyb ((l1 ++ l2) ++ l3) l4 ->
  PPermut_Hyb (l1 ++ (l2 ++ l3)) l4.
intros; rew_app in *; auto.
Qed.

Lemma PPermut_Hyb_tactic_simpl : forall l1 l2 l3 l4,
  PPermut_Hyb (l1 ++ l3) l4 ->
  PPermut_Hyb (l1 ++ (l2 ++ l3)) (l2 ++ l4).
intros; rewrite <- H; apply PPermut_Hyb_get_2.
Qed.

Lemma PPermut_Hyb_tactic_trans : forall l1 l2 l3,
  PPermut_Hyb l3 l2 -> PPermut_Hyb l1 l3 -> PPermut_Hyb l1 l2.
intros; eauto with ppermut_rew.
Qed.

Hint Rewrite app_assoc app_nil_l app_nil_r : ppermut_rew.

Ltac PPermut_Hyb_lemma_get n :=
  match nat_from_number n with
  | 1 => constr:(PPermut_Hyb_get_1)
  | 2 => constr:(PPermut_Hyb_get_2)
  | 3 => constr:(PPermut_Hyb_get_3)
  | 4 => constr:(PPermut_Hyb_get_4)
  | 5 => constr:(PPermut_Hyb_get_5)
  end.

Ltac PPermut_Hyb_isolate_cons :=
  do 20 try (* todo : repeat *)
    match goal with |- context [?x::?l] =>
      match l with
      | nil => fail 1
      | _ => rewrite <- (@app_cons_one _ x l)
      end
    end.

Ltac PPermut_Hyb_simpl_prepare :=
   autorewrite with ppermut_rew;
   PPermut_Hyb_isolate_cons;
   autorewrite with ppermut_rew;
   apply PPermut_Hyb_tactic_setup;
   repeat rewrite app_assoc.

Ltac PPermut_Hyb_index_of l lcontainer :=
  match constr:(lcontainer) with
  | l ++ _ => constr:(1)
  | _ ++ l ++ _ => constr:(2)
  | _ ++ _ ++ l ++ _ => constr:(3)
  | _ ++ _ ++ _ ++ l ++ _ => constr:(4)
  | _ ++ _ ++ _ ++ _ ++ l ++ _ => constr:(5)
  | _ ++ _ ++ _ ++ _ ++ _ ++ l ++ _ => constr:(6)
  | _ => constr:(0) (* not found *)
  end.

Ltac PPermut_Hyb_simpl_once :=
  match goal with
  | |- PPermut_Hyb (_ ++ nil) _ => fail 1
  | |- PPermut_Hyb (_ ++ (?l ++ _)) ?l' =>
     match PPermut_Hyb_index_of l l' with
     | 0 => apply PPermut_Hyb_tactic_keep
     | ?n => let F := PPermut_Hyb_lemma_get n in
            eapply PPermut_Hyb_tactic_trans;
            [ apply F
            | apply PPermut_Hyb_tactic_simpl ]
     end
  end.

Ltac PPermut_Hyb_simpl :=
  PPermut_Hyb_simpl_prepare;
  repeat PPermut_Hyb_simpl_once;
  autorewrite with ppermut_rew;
  try apply PPermut_Hyb_reflexive;
  auto.


(*** Other lemmas ***)
(* Note:
   Some are covered by PPermut_Hyb_simpl tactic, but we want to use them
   in auto! *)

Lemma PPermut_Hyb_Mem:
forall G G' w X,
  G ~=~ G' ->
  Mem (w, X) G ->
  exists X', X' *=* X /\ Mem (w, X') G'.
intros; generalize dependent X; induction H; intros.
rewrite Mem_nil_eq in H0; contradiction.
rewrite Mem_cons_eq in H1; destruct H1.
inversion H1; subst; exists Gamma'; split; [ symmetry | apply Mem_here]; auto.
apply IHPPermut_Hyb in H1; destruct H1 as (Gamma''); exists Gamma'';
destruct H1; split; auto; rewrite Mem_cons_eq; right; auto.
repeat rewrite Mem_cons_eq in H1; destruct H1.
inversion H1; subst; exists Gamma1; split; [ symmetry | rewrite Mem_cons_eq];
auto; right; apply Mem_here.
destruct H1.
inversion H1; subst; exists Gamma1'; split; [ symmetry | rewrite Mem_cons_eq];
auto.
exists X; split; auto; repeat rewrite Mem_cons_eq; right; right; auto.
apply IHPPermut_Hyb1 in H1; destruct H1 as (X'); destruct H1.
apply IHPPermut_Hyb2 in H2; destruct H2 as (X''); destruct H2;
exists X''; split; auto; transitivity X'; auto.
Qed.

Lemma PPermut_Hyb_nil_impl:
forall L,
  nil ~=~ L -> L = nil.
intros; remember (@nil ctx_Hyb) as L' in H;
induction H; intros;
discriminate || auto.
Qed.

Lemma PPermut_Hyb_nil_contr:
forall L a,
  ~ (PPermut_Hyb nil (a::L)).
induction L; intros; intro;
apply PPermut_Hyb_nil_impl in H; discriminate.
Qed.

Hint Resolve PPermut_Hyb_nil_impl PPermut_Hyb_nil_contr.

(* Based on Sorting/Permutation/Permutation_ind_bis *)
Theorem PPermut_Hyb_ind_bis :
 forall P : list ctx_Hyb -> list ctx_Hyb -> Prop,
   P nil nil ->
   (forall w x y l l', l ~=~ l' -> P l l' ->
     x *=* y -> P ((w,x) :: l) ((w,y) :: l')) ->
   (forall w w' x x' y y' l l', l ~=~ l' -> P l l' -> x *=* x' -> y *=* y' ->
     P ((w', y) :: (w, x) :: l) ((w, x') :: (w', y') :: l')) ->
   (forall l l' l'', l ~=~ l' -> P l l' -> l' ~=~ l'' -> P l' l'' -> P l l'') ->
   forall l l', l ~=~ l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans;
  intros; induction H; auto.
  apply Htrans with ((w', Gamma0')::(w, Gamma0)::G); auto.
    apply Hswap; auto; induction G; auto; destruct a; apply Hskip; auto.
    apply Hskip; auto; apply Hskip; auto; induction G; auto;
    destruct a; apply Hskip; auto.
  eauto.
Qed.

Lemma PPermut_Hyb_app_rev:
forall G G' H H' w a a',
  a *=* a' ->
  G & (w, a) ++ G' ~=~ H & (w, a') ++ H' ->
  G ++ G' ~=~ H ++ H'.
Proof.
  set (P l l' :=
         forall w a a' l1 l2 l3 l4, a *=* a' ->
         l=l1 & (w, a) ++ l2 -> l'=l3 & (w, a') ++l4 -> (l1++l2) ~=~ (l3++l4)).
  cut (forall l l', l ~=~ l' -> P l l').
  intros; apply (H _ _ H2 w a a'); auto.
  intros; apply (PPermut_Hyb_ind_bis P); unfold P; clear P;
    try clear H l l'; simpl; auto.
  (* nil *)
  intros; destruct l1; simpl in *; discriminate.
  (* skip *)
  intros w x y l l' H IH; intros.
  destruct l1; destruct l3; rew_app in *;
  inversion H2; inversion H3; subst; auto.
    rewrite H; PPermut_Hyb_simpl; constructor; [transitivity a |] ; auto;
      symmetry; auto.
    rewrite <- H; PPermut_Hyb_simpl; constructor; auto; transitivity a';
      [ | symmetry]; auto.
  constructor; auto.
  apply (IH w0 a a' l1 l2 l3 l4); rew_app; auto.
  (* swap *)
  intros w w' x x' y y' l l' Hp IH; intros.
  destruct l1; destruct l2; rew_app in *; subst;
  inversion H2; subst; auto; try rewrite Hp; rew_app;
  PPermut_Hyb_simpl; destruct l3; destruct l4; rew_app in *; subst;
  inversion H3; subst; auto.
    constructor; auto; transitivity a'; auto; transitivity a; auto;
    symmetry; auto.
    constructor; auto; destruct l3; rew_app in *; inversion H6; subst; auto;
      PPermut_Hyb_simpl; constructor; auto; transitivity a; auto; symmetry; auto.
    constructor; auto; destruct l3; rew_app in *; inversion H6; subst; auto;
      PPermut_Hyb_simpl; constructor; auto; transitivity a; auto; symmetry; auto.
    constructor; auto; destruct l1; rew_app in *; inversion H6; subst; auto;
      PPermut_Hyb_simpl; rewrite <- Hp; PPermut_Hyb_simpl; constructor; auto;
      transitivity a'; auto; symmetry; auto.
  destruct l1; destruct l3; rew_app in *; inversion H6; inversion H7; subst;
    auto.
      constructor; auto; transitivity a'; auto; transitivity a; auto;
        symmetry; auto.
       apply PPermut_Hyb_nil_impl in Hp; destruct l3; rew_app in *; discriminate.
       symmetry in Hp; apply PPermut_Hyb_nil_impl in Hp; destruct l1;
         rew_app in *; discriminate.
       transitivity ((w', y') :: (w, x') :: l1).
         constructor; [ | constructor]; auto.
         PPermut_Hyb_simpl.
       replace l1 with (l1 ++ nil) by (rew_app; auto);
       replace l3 with (l3 ++ nil) by (rew_app; auto);
       apply IH with (w:=w0) (a0:=a) (a'0:=a'); auto;
         rew_app; auto.
  destruct l1; destruct l3; rew_app in *; inversion H6; inversion H7; subst;
    auto.
       apply PPermut_Hyb_nil_impl in Hp; discriminate.
       apply PPermut_Hyb_nil_impl in Hp; destruct l3; rew_app in *; discriminate.
       rewrite <- Hp; PPermut_Hyb_simpl; transitivity ((w,x)::(w0,y)::nil);
         PPermut_Hyb_simpl; constructor; auto; constructor; auto;
         transitivity a'; auto; symmetry; auto.
       transitivity ((w',y')::(w,x')::l1); auto; PPermut_Hyb_simpl; rew_app;
       replace l1 with (l1 ++ nil) by (rew_app; auto);
       apply IH with (w:=w0) (a0:=a) (a'0:=a'); auto;
         rew_app; auto.
  constructor; auto; rewrite <- Hp; symmetry; destruct l1; rew_app in *;
    inversion H6; subst; auto; PPermut_Hyb_simpl; constructor; auto;
    transitivity a'; auto; symmetry; auto.
  destruct l3; rew_app in *; inversion H7; subst.
    symmetry in Hp; apply PPermut_Hyb_nil_impl in Hp; subst; inversion H6; subst;
      destruct l1; rew_app in *; inversion H6; subst; destruct l1; rew_app in *;
      discriminate.
    transitivity ((w', y') ::l1 ++ p0 :: l2); PPermut_Hyb_simpl; rew_app.
    destruct l1; rew_app in *; inversion H6; subst.
      rewrite Hp; PPermut_Hyb_simpl; constructor; auto; transitivity a; auto;
      symmetry; auto.
      constructor; auto; replace l3 with (l3 ++ nil) by (rew_app; auto);
      apply IH with (w:=w0) (a0:=a) (a'0:=a'); auto; rew_app; auto.
  clear H2 H3. destruct l1; destruct l3; rew_app in *; inversion H6;
  inversion H7; subst.
    constructor; auto; transitivity a; auto; transitivity a'; auto;
    symmetry; auto.
    transitivity ((w', y'):: p0 :: l2).
      constructor; auto.
      PPermut_Hyb_simpl. clear H6 H7. rew_app; rewrite Hp; PPermut_Hyb_simpl;
      constructor; auto; transitivity a; auto; symmetry; auto.
    transitivity ((w, x)::p1::l4).
      PPermut_Hyb_simpl; rew_app; rewrite <- Hp; PPermut_Hyb_simpl; constructor;
        auto; transitivity a'; auto; symmetry; auto.
      constructor; auto.
    transitivity ((w', y') :: (w, x') :: l1 ++ p0 :: l2).
      constructor; auto; constructor; auto.
      PPermut_Hyb_simpl. clear H7 H6. rew_app.
    apply IH with (w:=w0) (a0:=a) (a'0:=a'); rew_app; auto.
  (* trans *)
  intros. destruct (PPermut_Hyb_Mem l l' w a) as (a'', (H6a, H6b)); auto.
    subst; rewrite Mem_app_or_eq; left; rewrite Mem_app_or_eq; right;
      apply Mem_here.
  destruct (Mem_split ctx_Hyb l' (w, a'')) as (l'1, (l'2, H6)); auto.
  transitivity (l'1 ++ l'2).
    apply H0 with (w:=w) (a:=a) (a':=a''); [ symmetry | | ]; auto.
    apply H2 with (w:=w) (a:=a'') (a':=a').
      transitivity a; auto; symmetry; auto.
      auto.
      auto.
Qed.

Lemma PPermut_Hyb_last_rev_simpl:
forall G G' a,
  G & a ~=~ G' & a ->
  G ~=~ G'.
intros; replace G with (G ++ nil) by (rew_app; auto);
replace G' with (G'++nil) by (rew_app; auto);
destruct a;
apply PPermut_Hyb_app_rev with (w:=v)(a:=l)(a':=l); rew_app; eauto.
Qed.

Lemma PPermut_Hyb_last_rev:
forall G G' w Gamma Gamma',
  Gamma *=* Gamma' ->
  G & (w, Gamma) ~=~ G' & (w, Gamma') ->
  G ~=~ G'.
intros;
assert (G & (w, Gamma) ~=~ G' & (w, Gamma)) by eauto with ppermut_rew;
apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma)); auto.
Qed.

Lemma PPermut_Hyb_split_head:
forall G G' w Gamma,
  (w, Gamma) :: G ~=~ G' ->
  exists Gamma' hd tl,
    Gamma *=* Gamma' /\ G' = hd & (w, Gamma') ++ tl.
intros.
apply PPermut_Hyb_Mem with (w:=w) (X:=Gamma) in H.
destruct H as (Gamma'); destruct H.
exists Gamma'.
assert (exists hd, exists tl, G' = hd & (w, Gamma') ++ tl) by
  (eapply Mem_split; auto).
destruct H1 as (hd, (tl, H1));
exists hd; exists tl; split; [symmetry | ]; auto.
apply Mem_here.
Qed.

Lemma PPermut_Hyb_split_neq:
forall G G' w w' Gamma Gamma',
  G & (w, Gamma) ~=~ G' & (w', Gamma') ->
  ~Gamma *=* Gamma' \/ w <> w' ->
  exists Gamma0, exists GH, exists GT,
    Gamma0 *=* Gamma' /\
    G = GH & (w', Gamma0) ++ GT.
intros.
assert ((w, Gamma) ::G  ~=~ (G' & (w', Gamma'))) by
  (transitivity (G & (w,Gamma)); auto; PPermut_Hyb_simpl).
assert ((w, Gamma) :: G ~=~ (w', Gamma') :: G') by
  (transitivity (G' & (w', Gamma')); auto; PPermut_Hyb_simpl).
symmetry in H2;
apply PPermut_Hyb_split_head in H2;
destruct H2 as (Gamma'',(GH, (GT, (Ha, Hb)))).
destruct GH; rew_app in *.
inversion Hb; subst; destruct H0; elim H0; symmetry; auto.
destruct p; inversion Hb; subst.
exists Gamma''; exists GH; exists GT; split;
[symmetry | rew_app]; auto.
Qed.

Lemma PPermut_Hyb_swap2:
forall C C' G,
  C :: G & C' ~=~ G & C & C'.
intros; PPermut_Hyb_simpl.
Qed.
Hint Resolve PPermut_Hyb_swap2.

Lemma PPermut_Hyb_middle_last:
forall G G' C,
  G ++ G' & C ~=~ G ++ C :: G'.
intros; PPermut_Hyb_simpl.
Qed.
Hint Resolve PPermut_Hyb_middle_last.

Lemma PPermut_Hyb_specialized1:
forall G G' C C',
  G ++ C :: G' & C' ~=~ G ++ G' ++ C' :: C :: nil.
intros; PPermut_Hyb_simpl.
Qed.

Lemma PPermut_Hyb_specialized2:
forall GH GT G Gamma Gamma' Gamma'',
  GH ++ Gamma :: GT & Gamma' ~=~ G & Gamma ->
  GH ++ GT ++ Gamma'' :: Gamma' :: nil ~=~ G & Gamma''.
intros; PPermut_Hyb_simpl;
apply PPermut_Hyb_last_rev_simpl with (a:=Gamma);
rewrite <- H; PPermut_Hyb_simpl.
Qed.

Lemma PPermut_Hyb_specialized3:
forall G G' C C',
  G ++ G' ++ C :: C' :: nil ~=~ G ++ C :: G' & C'.
intros; PPermut_Hyb_simpl.
Qed.

Lemma PPermut_Hyb_specialized4:
forall G GH GT Gamma Gamma0 Gamma'0,
  GH ++ Gamma :: GT & Gamma'0 ~=~ G & Gamma ->
  G ++ Gamma0 :: Gamma :: nil ~=~ GH ++ GT ++ Gamma0 :: Gamma'0 :: Gamma :: nil.
intros; PPermut_Hyb_simpl;
apply PPermut_Hyb_last_rev_simpl with (a:=Gamma); rewrite <- H;
PPermut_Hyb_simpl.
Qed.

Lemma PPermut_Hyb_specialized5:
forall G G' C C' C'',
  G ++ C :: G' ++ C' :: C'' :: nil ~=~ (G ++ G' ++ C' :: C'' :: nil) & C.
intros; PPermut_Hyb_simpl.
Qed.

Lemma PPermut_Hyb_specialized6:
forall GH GT C0 C'' C'0,
  GH ++ GT ++ C'0 :: C'' :: C0 :: nil ~=~ GH ++ GT ++ C0 :: C'0 :: C'' :: nil.
intros; PPermut_Hyb_simpl.
Qed.

Lemma PPermut_Hyb_swap_inner:
forall G G' C C',
  C :: G ++ C' :: G' ~=~ C' :: G ++ G' & C.
intros; PPermut_Hyb_simpl.
Qed.

Lemma PPermut_Hyb_swap_inner2:
forall G G' C C',
  C :: G ++ G' & C' ~=~ C' :: G ++ G' & C.
intros; PPermut_Hyb_simpl.
Qed.

Lemma PPermut_Hyb_swap3:
forall C C' G,
  C :: G & C' ~=~ C' :: G & C.
intros; PPermut_Hyb_simpl.
Qed.

Lemma PPermut_Hyb_swap4:
forall C G' G,
  G ++ G' & C ~=~ G & C ++ G'.
intros; PPermut_Hyb_simpl.
Qed.

Hint Resolve PPermut_Hyb_swap_inner.
Hint Resolve PPermut_Hyb_swap_inner2.
Hint Resolve PPermut_Hyb_swap3 PPermut_Hyb_swap4.

Hint Resolve PPermut_Hyb_specialized2 : ppermut_rew.
Hint Resolve PPermut_Hyb_specialized1
             PPermut_Hyb_specialized3 PPermut_Hyb_specialized4
             PPermut_Hyb_specialized5 PPermut_Hyb_specialized6.

Lemma permut_PPermut_Hyb:
forall G G', G *=* G' -> G ~=~ G'.
intros. induction H; auto.
transitivity y; auto.
inversion H. PPermut_Hyb_simpl.
Qed.

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


Close Scope permut_scope.
