Require Export Syntax.
Require Export Substitution.
Require Import FSets.
Require Import List.
Require Import Metatheory.

Open Scope is5_scope.

Global Reserved Notation " G '|=' Gamma '|-' M ':::' A " (at level 70).

Definition Context := list ty.

(* Statics *)

Inductive types: fset Context -> Context -> te -> ty -> Prop :=
| t_hyp: forall A G Gamma v_n
  (HT: nth_error Gamma v_n = Some A),
  G |= Gamma |- (hyp v_n) ::: A
| t_lam: forall A B G Gamma M 
  (HT: G |= A::Gamma |- M ::: B),
  G |= Gamma |- (lam A M) ::: A ---> B
| t_appl: forall A B G Gamma M N
  (HT1: G |= Gamma |- M ::: A ---> B)
  (HT2: G |= Gamma |- N ::: A),
  G |= Gamma |- (appl M N) ::: B
| t_box: forall A G Gamma M
  (HT: \{Gamma} \u G |= nil |- M ::: A),
  G |= Gamma |- (box M) ::: [*] A
| t_unbox: forall A G Gamma M
  (HT: G |= Gamma |- M ::: [*] A),
  G |= Gamma |- unbox M ::: A
| t_unbox_fetch: forall A G Gamma1 Gamma2 M
  (HIn: Gamma2 \in G)
  (HT: \{Gamma1} \u G \- \{Gamma2} |= Gamma2 |- M ::: [*] A),
  G |= Gamma1 |- unbox_fetch M ::: A
| t_here: forall A G Gamma M
  (HT: G |= Gamma |- M ::: A),
  G |= Gamma |- here M ::: <*> A
| t_get_here: forall A G Gamma1 Gamma2 M
  (HIn: Gamma2 \in G)
  (HT: \{Gamma1} \u G \- \{Gamma2}|= Gamma2 |- M ::: A),
  G |= Gamma1 |- get_here M ::: <*> A
| t_letdia: forall A B G Gamma M N
  (HT1: G |= Gamma |- M ::: <*> A)
  (HT2: \{A::nil} \u G |= Gamma |- N ::: B),
  G |= Gamma |- letdia M N ::: B
| t_letdia_get: forall A B G Gamma1 Gamma M N
  (HIn: Gamma \in G)
  (HT1: \{Gamma1} \u G \- \{Gamma}|= Gamma |- M ::: <*> A)
  (HT2: \{A::nil} \u G |= Gamma1 |- N ::: B),
  G |= Gamma1 |- letdia_get M N ::: B
where " G '|=' Gamma '|-' M ':::' A " := (types G Gamma M A).

(* Dynamics *)

Inductive value: te -> Prop :=
| val_lam: forall A M, value (lam A M)
| val_box: forall M, value (box M)
| val_here: forall M, value M -> value (here M)
| val_get_here: forall M, value M -> value (get_here M)
.

Global Reserved Notation " M |-> N " (at level 70).

Inductive step: te -> te -> Prop :=
| red_appl_lam: forall M A N, appl (lam A M) N |-> [N//0] M
| red_unbox_box: forall M, unbox (box M) |-> M
| red_unbox_fetch_box: forall M, unbox_fetch (box M) |-> M
| red_letdia_here: forall M N, letdia (here M) N |-> [M//0]N
| red_letdia__get_here: forall M N, letdia (get_here M) N |-> [M//0]N
| red_letdia_get__here: forall M N, letdia_get (here M) N |-> [M//0]N
| red_letdia_get_get_here: forall M N, letdia_get (get_here M) N |-> [M//0]N
| red_appl: forall M N M' (HT: M |-> M'), appl M N |-> appl M' N
| red_unbox: forall M M' (HT: M |-> M'), unbox M |-> unbox M'
| red_unbox_fetch: forall M M' (HT: M |-> M'), unbox_fetch M |-> unbox_fetch M'
| red_dia_here: forall M M' (HT: M |-> M'), here M |-> here M'
| red_dia_move: forall M M' (HT: M |-> M'), get_here M |-> get_here M'
| red_letdia: forall M N M' (HT: M |-> M'), letdia M N |-> letdia M' N
| red_letdia_move: forall M N M' (HT: M |-> M'), letdia_get M N |-> letdia_get M' N
where " M |-> N " := (step M N ) : is5_scope.


Section Lemmas.

Lemma eq_context_dec:
forall Gamma Gamma': Context, {Gamma = Gamma'} + {Gamma <> Gamma'}.
  intros; decide equality; decide equality.
Qed.

Lemma BackgroundImpl:
forall G G' Gamma M A
  (HEq: forall A, A \in G -> A \in G')
  (HT: G |= Gamma |- M ::: A),
  G' |= Gamma |- M ::: A.
intros; generalize dependent G'; induction HT; intros; eauto using types.
(* box *)
constructor; apply IHHT;
intros.
rewrite in_union in H; destruct H; rewrite in_union; 
try (right; apply HEq; assumption); 
rewrite in_singleton in H; subst; left; rewrite in_singleton; reflexivity.
(* unbox_fetch *)
apply t_unbox_fetch with (Gamma2:=Gamma2);
[apply HEq; assumption | apply IHHT];
intros; destruct (eq_context_dec A0 Gamma2).
(* A0 = Gamma2 *)
subst; intros; rewrite in_union in H.
  destruct H; rewrite in_union;
  [rewrite in_singleton in H; subst | rewrite in_remove in H; destruct H].
    left; rewrite in_singleton; reflexivity.
    rewrite notin_singleton in H0; elim H0; reflexivity.
(* A0 <> Gamma *)
intros; rewrite in_union in H; rewrite in_union; destruct H.
  left; assumption. 
  right; rewrite in_remove in H; rewrite in_remove; destruct H; split;
  [apply HEq| ]; assumption.
(* get_here *)
apply t_get_here with (Gamma2:=Gamma2);
[apply HEq; assumption | apply IHHT]; 
intros; destruct (eq_context_dec A0 Gamma2).
(* A0 = Gamma2 *)
subst; intros; rewrite in_union in H.
  destruct H; rewrite in_union;
  [rewrite in_singleton in H; subst | rewrite in_remove in H; destruct H].
    left; rewrite in_singleton; reflexivity.
    rewrite notin_singleton in H0; elim H0; reflexivity.
(* A0 <> Gamma *)
intros; rewrite in_union in H; rewrite in_union; destruct H.
  left; assumption. 
  right; rewrite in_remove in H; rewrite in_remove; destruct H; split;
  [apply HEq| ]; assumption.
(* letdia *)
apply t_letdia with (A:=A).
  apply IHHT1; assumption.
  apply IHHT2; intros; 
    rewrite in_union in H; destruct H; rewrite in_union.
      left; assumption.
      right; apply HEq; assumption.
(* letdia_get *)
apply t_letdia_get with (A:=A) (Gamma:=Gamma).
  apply HEq; assumption.
  apply IHHT1; intros.
    rewrite in_union in H; destruct H; rewrite in_union.
      left; assumption.
      rewrite in_remove in H; destruct H;
      right; rewrite in_remove; split.
        apply HEq; assumption.
        assumption.
   apply IHHT2; intros.
    rewrite in_union in H; destruct H; rewrite in_union.
      left; assumption.
      right; apply HEq; assumption.
Qed.

Lemma GlobalWeakening:
forall G Gamma M A Ctx
  (HT: G |= Gamma |- M ::: A),
  G \u \{Ctx} |= Gamma |- M ::: A.
intros.
apply BackgroundImpl with (G:=G).
intros.
rewrite in_union; left; assumption.
assumption.
Qed.

Lemma Progress:
forall G M A
  (EmptyCtx: forall Ctx, Ctx \in G -> Ctx = nil)
  (HT: G |= nil |- M ::: A),
  value M \/ exists N, M |-> N.
induction M; intros; eauto using value.
(* hyp *)
inversion HT; destruct n; discriminate.
(* appl *)
right.
inversion HT; subst.
destruct (IHM1 (A0 ---> A) EmptyCtx HT1).
  inversion H; subst; inversion HT1; subst; eexists; constructor.
  destruct H; eexists; constructor; eapply H.
(* unbox *)
right.
inversion HT; subst.
destruct (IHM ([*]A) EmptyCtx HT0).
  inversion H; subst; inversion HT0; subst; eexists; constructor.
  destruct H; eexists; constructor; eapply H.
(* unbox_fetch *)
right; inversion HT; subst.
destruct (IHM ([*]A) EmptyCtx).
apply BackgroundImpl with (G:=\{nil} \u G \- \{nil}).
intros; rewrite in_union in H; rewrite in_remove in H; destruct H.
rewrite in_singleton in H; subst.
assert (Gamma2 = nil); auto.
subst; assumption.
destruct H; assumption.
apply EmptyCtx in HIn; subst; assumption.
inversion H; subst; inversion HT0; subst.
  eexists; constructor.
destruct H; eexists; constructor; eauto.
(* here *)
inversion HT; subst.
destruct (IHM A0 EmptyCtx HT0).
left; apply val_here; assumption.
right; destruct H. exists (here x); eauto using step.
(* get_here *)
inversion HT; subst.
destruct (IHM A0 EmptyCtx).
apply BackgroundImpl with (G:=\{nil} \u G \- \{nil}).
intros; rewrite in_union in H; rewrite in_remove in H; destruct H.
rewrite in_singleton in H; subst.
assert (Gamma2 = nil); auto.
subst; assumption.
destruct H; assumption.
apply EmptyCtx in HIn; subst. assumption.
left; econstructor; eassumption.
right; destruct H; exists (get_here x); eauto using step.
(* letdia *)
right; inversion HT; subst.
destruct (IHM1 (<*>A0) EmptyCtx HT1).
inversion H; subst; inversion HT1; subst.
  exists [M//0]M2; eauto using step.
  exists [M//0]M2; eauto using step.
destruct H; exists (letdia x M2); eauto using step.
(* letdia_get *)
right; inversion HT; subst.
destruct (IHM1 (<*>A0) EmptyCtx).
apply BackgroundImpl with (G:=\{nil} \u G \- \{nil}).
intros; rewrite in_union in H; rewrite in_remove in H; destruct H.
rewrite in_singleton in H; subst.
assert (Gamma = nil); auto.
subst; assumption.
destruct H; assumption.
apply EmptyCtx in HIn; subst. assumption.
inversion H; subst; inversion HT1; subst.
  exists [M//0]M2; eauto using step.
  exists [M//0]M2; eauto using step.
destruct H; exists (letdia_get x M2); eauto using step.
Qed.

End Lemmas.

Close Scope is5_scope.