Require Export Syntax.
Require Export Substitution.
Require Import LibList.
Require Import LibListSorted.
Require Import LibRelation.

(*
(* Test standard permutations *)
Require Import List.
Require Import Sorting.Permutation.

(* Notations & definitions *)
Notation "l & x" := (l ++ (x::nil)) 
  (at level 28, left associativity) : list_scope.
Definition permut := (@Permutation (list ty)).

Lemma PermutLastSame:
forall G G' elem
  (HT: permut (G & elem) (G' & elem)),
  permut G G'.
intros;
apply Permutation_app_inv_r in HT.
assumption.
Qed.

Lemma InConsNeq:
forall A G (elem:A) elem',
  elem<>elem' -> In elem (G&elem') -> In elem G.
intros.
apply in_app_or in H0.
destruct H0.
assumption.
apply in_inv in H0. destruct H0.
symmetry in H0; contradiction.
apply in_nil in H0; contradiction.
Qed.

Lemma PermutationElementSplit_Neq:
forall G G' H elem elem'
  (HNeq: elem <> elem')
  (HT: permut (G & elem ++ G') (H & elem')),
  exists GH, exists GT, H = GH & elem ++ GT.
intros.
assert (exists G0, exists G1, H = G0 ++ elem::G1). 
apply in_split.
apply InConsNeq with (elem':=elem').
assumption.
apply Permutation_in with (l:=G & elem ++ G').
assumption.
apply in_or_app.
left; apply in_or_app.
right; apply in_eq.
(* after assert *)
destruct H0 as [GH]; destruct H0 as [GT];
exists GH; exists GT.
subst H;
rewrite <- app_assoc.
simpl; reflexivity.
Qed.

(* / *)
*)

Open Scope is5_scope.

Global Reserved Notation " G '|=' Gamma '|-' M ':::' A " (at level 70).

Definition Context := list ty.

(* Statics *)
Inductive types: list Context -> Context -> te -> ty -> Prop :=
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
  (HT: G & Gamma |= nil |- M ::: A),
  G |= Gamma |- (box M) ::: [*] A
| t_unbox: forall A G Gamma M
  (HT: G |= Gamma |- M ::: [*] A),
  G |= Gamma |- unbox M ::: A
| t_unbox_fetch: forall A G Gamma Gamma' M
  (HT: G & Gamma' |= Gamma |- M ::: [*] A),
  forall G0, permut (G & Gamma) G0 -> G0 |= Gamma' |- unbox_fetch M ::: A
| t_here: forall A G Gamma M
  (HT: G |= Gamma |- M ::: A),
  G |= Gamma |- here M ::: <*> A
| t_get_here: forall A G Gamma Gamma' M
  (HT: G & Gamma' |= Gamma |- M ::: A),
  forall G0, permut (G & Gamma) G0 -> G0 |= Gamma' |- get_here M ::: <*> A
| t_letdia: forall A B G Gamma M N
  (HT1: G |= Gamma |- M ::: <*> A)
  (HT2: (A :: nil) :: G |= Gamma |- N ::: B),
  G |= Gamma |- letdia M N ::: B 
| t_letdia_get: forall A B G Gamma Gamma' M N
  (HT1: G & Gamma' |= Gamma |- M ::: <*> A)
  (HT2: (A :: nil) :: G & Gamma |= Gamma' |- N ::: B),
  forall G0, permut (G & Gamma) G0 -> G0 |= Gamma' |- letdia_get M N ::: B
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

(* TODO: this may be moved to a separate file *)

(* Permutation *)

Lemma PermutLastSame:
forall A G G' (elem:A)
  (HT: permut (G & elem) (G' & elem)),
  permut G G'.
Admitted.

Lemma PermutationElementSplit_Neq:
forall A G G' H (elem:A) (elem':A)
  (HNeq: elem <> elem')
  (HT: permut (G & elem ++ G') (H & elem')),
  exists GH, exists GT, H = GH & elem ++ GT.
Admitted.

(* / Permutation *)

(* TODO: not automated enough *)
Lemma BackgroundSubsetImpl:
forall G G' Gamma M A
  (HT: G |= Gamma |- M ::: A)
  (HSubst: exists GT, permut (G++GT) G'),
  G' |= Gamma |- M ::: A.
intros.
generalize dependent G'.
induction HT; intros; eauto using types.
(* box *)
destruct HSubst as [GT];
constructor;
apply IHHT;
exists GT; permut_simpl; assumption.
(* unbox_fetch *)
destruct HSubst as [GT];
apply t_unbox_fetch with (Gamma:=Gamma) (G:=G++GT).
apply IHHT;
  exists GT; permut_simpl.
apply permut_trans with (l2:= G0 ++ GT); 
[ permut_simpl | ]; assumption.
(* get_here *)
destruct HSubst as [GT];
apply t_get_here with (Gamma:=Gamma) (G:=G++GT).
apply IHHT;
  exists GT; permut_simpl.
apply permut_trans with (l2:= G0 ++ GT); 
[ permut_simpl | ]; assumption.
(* letdia *)
apply t_letdia with (A:=A). 
apply IHHT1; assumption.
apply IHHT2; destruct HSubst as [GT];
exists GT; permut_simpl; assumption.
(* letdia_get *)
destruct HSubst as [GT];
apply t_letdia_get with (A:=A)(Gamma:=Gamma) (G:=G++GT).
apply IHHT1;
  exists GT; permut_simpl.
apply IHHT2;
  exists GT; permut_simpl.
apply permut_trans with (l2:= G0 ++ GT); 
[ permut_simpl | ]; assumption.
Qed.

Lemma GlobalWeakening:
forall G G' Gamma M A Ctx
  (HT: G ++ G' |= Gamma |- M ::: A),
  G & Ctx ++ G' |= Gamma |- M ::: A.
intros; rew_app;
apply BackgroundSubsetImpl with (G:=G++G');
[assumption | exists (Ctx::nil); permut_simpl].
Qed.

(* TODO: ugly!!!... *)
Lemma Weakening_general:
forall G Gamma M A
  (HT: G |= Gamma |- M ::: A),
  (forall G' Delta Delta',
    permut G (G' & Delta) ->
    G' & (Delta ++ Delta') |= Gamma |- M ::: A) /\ 
  (forall Gamma', G |= Gamma ++ Gamma' |- M ::: A).
intros.
induction HT; split; intros.
(* hyp *)
eauto using types.
constructor; generalize dependent v_n;
induction Gamma; destruct v_n; intros;
simpl in HT; try discriminate; simpl;
[ | apply IHGamma]; assumption.
(* lam *)
constructor; eapply IHHT; eassumption.
constructor; eapply IHHT; eassumption.
(* appl *)
econstructor; [eapply IHHT1| eapply IHHT2]; eauto.
econstructor; [eapply IHHT1| eapply IHHT2]; eauto.
(* box 1 *)
constructor;
apply BackgroundSubsetImpl with (G:=G' & Gamma & (Delta ++ Delta')).
  eapply IHHT.
    permut_simpl; assumption.
  exists nil; permut_simpl; assumption.
(* box 2 *)
constructor;
apply IHHT; permut_simpl.
(* unbox *)
constructor; apply IHHT; assumption.
constructor; apply IHHT; assumption.
(* unbox_fetch 1 *)
destruct (eq_context_dec Gamma Delta).
(* = *)
subst;
apply t_unbox_fetch with (Gamma:=Delta++Delta') (G:=G).
  apply IHHT.
  apply permut_app_l;
  apply PermutLastSame with (elem:=Delta); (* sad panda 8( *)
  apply permut_trans with (l2:=G0); assumption.
(* <> *)
assert (exists G0, exists G1, G' = G0 & Gamma ++ G1).
  (* very sad panda 8( *)
  apply PermutationElementSplit_Neq with (G:=G) (G':=nil) (elem':=Delta).
    assumption.
    rew_app; apply permut_trans with (l2:=G0); assumption.
destruct H1 as [GH]; destruct H1 as [GT]; subst G';
apply t_unbox_fetch with (Gamma:=Gamma) (G:=GH ++ GT & (Delta ++ Delta')).
apply BackgroundSubsetImpl with (G:= (GH ++ GT & Gamma') & (Delta ++ Delta')).
  apply IHHT; permut_simpl;
  apply PermutLastSame with (elem := Gamma);
  apply permut_trans with (l2:=G0).
    assumption.
    apply permut_trans with (l2:=(GH & Gamma ++ GT) & Delta).
      assumption.
      permut_simpl.
  exists nil; permut_simpl.
permut_simpl.
(* unbox_fetch 2 *)
apply t_unbox_fetch with (G:=G) (Gamma:=Gamma).
  apply IHHT; permut_simpl.
  assumption.
(* here *)
constructor; apply IHHT; assumption.
constructor; apply IHHT; assumption.
(* get_here 1 *)
destruct (eq_context_dec Gamma Delta).
(* = *)
subst;
apply t_get_here with (Gamma:=Delta++Delta') (G:=G).
  apply IHHT.
  apply permut_app_l;
  apply PermutLastSame with (elem:=Delta); (* sad panda 8( *)
  apply permut_trans with (l2:=G0); assumption.
(* <> *)
assert (exists G0, exists G1, G' = G0 & Gamma ++ G1).
  apply PermutationElementSplit_Neq with (G:=G) (G':=nil) (elem':=Delta).
    assumption.
    rew_app; apply permut_trans with (l2:=G0); assumption.
destruct H1 as [GH]; destruct H1 as [GT]; subst G';
apply t_get_here with (Gamma:=Gamma) (G:=GH ++ GT & (Delta ++ Delta')).
apply BackgroundSubsetImpl with (G:= (GH ++ GT & Gamma') & (Delta ++ Delta')).
  apply IHHT; permut_simpl;
  apply PermutLastSame with (elem := Gamma);
  apply permut_trans with (l2:=G0).
    assumption.
    apply permut_trans with (l2:=(GH & Gamma ++ GT) & Delta).
      assumption.
      permut_simpl.
  exists nil; permut_simpl.
permut_simpl.
(* get_here 2 *)
apply t_get_here with (G:=G) (Gamma:=Gamma).
  apply IHHT; permut_simpl.
  assumption.
(* letdia *)
apply t_letdia with (A:=A).
apply IHHT1; assumption.
apply IHHT2 with (G':=(A::nil)::G'). 
permut_simpl.
assumption.
apply t_letdia with (A:=A).
apply IHHT1; assumption.
apply IHHT2. 
(* letdia_get 1 *)
destruct (eq_context_dec Gamma Delta).
(* = *)
subst;
apply t_letdia_get with (A:=A)(Gamma:=Delta++Delta') (G:=G).
apply IHHT1; assumption.
apply BackgroundSubsetImpl with (G:=((A::nil) :: G) & (Delta ++ Delta')).
  apply IHHT2; permut_simpl.
  exists nil; permut_simpl.
apply permut_app_l;
apply PermutLastSame with (elem:=Delta); (* sad panda 8( *)
apply permut_trans with (l2:=G0); assumption.
(* <> *)
assert (exists G0, exists G1, G' = G0 & Gamma ++ G1).
  apply PermutationElementSplit_Neq with (G:=G) (G':=nil) (elem':=Delta).
    assumption.
    rew_app; apply permut_trans with (l2:=G0); assumption.
destruct H1 as [GH]; destruct H1 as [GT];
subst G';
apply t_letdia_get with (A:=A)(Gamma:=Gamma) (G:=GH ++ GT & (Delta ++ Delta')).
(* <*> A*)
apply BackgroundSubsetImpl with (G:= (GH ++ GT & Gamma') & (Delta ++ Delta')).
  apply IHHT1;
  permut_simpl;
  apply PermutLastSame with (elem := Gamma);
  apply permut_trans with (l2:=G0).
    assumption.
    apply permut_trans with (l2:=(GH & Gamma ++ GT) & Delta).
      assumption.
      permut_simpl.
exists nil; permut_simpl.
(* B *)
apply BackgroundSubsetImpl with (G:=(((A :: nil) :: GH ++ GT & Gamma) & (Delta ++ Delta'))).
  apply IHHT2;
  permut_simpl;
  apply PermutLastSame with (elem := Gamma);
  apply permut_trans with (l2:=G0).
    assumption. 
    permut_simpl.
    apply permut_trans with (l2:=(GH & Gamma ++ GT) & Delta).
      assumption.
      permut_simpl.
  exists nil; permut_simpl.
permut_simpl.
(* letdia_get 2 *)
apply t_letdia_get with (A:=A)(G:=G) (Gamma:=Gamma).
apply IHHT1; permut_simpl.
apply IHHT2; permut_simpl.
assumption.
Qed.

Lemma WeakeningBackgroundElem:
forall G G' Delta Delta' Gamma M A
  (HT: G & Delta ++ G' |= Gamma |- M ::: A),
  G & (Delta ++ Delta') ++ G' |= Gamma |- M ::: A.
intros.
apply BackgroundSubsetImpl with (G:=(G++G') & (Delta ++ Delta')).
assert (permut (G & Delta ++ G') ((G++G') & Delta)).
  permut_simpl.
eapply Weakening_general; eassumption.
exists nil; permut_simpl.
Qed.

Lemma Weakening:
forall G Gamma Gamma' M A
  (HT: G |= Gamma |- M ::: A),
  G |= Gamma ++ Gamma' |- M ::: A.
intros;
eapply Weakening_general; eassumption.
Qed.

Lemma Progress:
forall G M A
  (EmptyCtx: forall G', 
    permut G G' -> 
    forall Ctx, Mem Ctx G' -> Ctx = nil)
  (HT: G |= nil |- M ::: A),
  value M \/ exists N, M |-> N.
induction M; intros; eauto using value.
(* hyp *)
inversion HT; destruct n; discriminate.
(* appl *)
right; inversion HT; subst;
destruct (IHM1 (A0 ---> A) EmptyCtx HT1).
  inversion H; subst; inversion HT1; subst; eexists; constructor.
  destruct H; eexists; constructor; eapply H.
(* unbox *)
right; inversion HT; subst;
destruct (IHM ([*]A) EmptyCtx HT0).
  inversion H; subst; inversion HT0; subst; eexists; constructor.
  destruct H; eexists; constructor; eapply H.
(* unbox_fetch *)
right; inversion HT; subst.
destruct (IHM ([*]A) EmptyCtx).
assert (Gamma = nil).
  apply EmptyCtx with (G':=G0 & Gamma).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq. right; rewrite Mem_cons_eq; left; reflexivity.
subst. 
apply BackgroundSubsetImpl with (G:=G0 & nil). 
assumption.
exists nil; rew_app; assumption.
inversion H; subst; inversion HT0; subst; eexists; constructor.
destruct H; eexists; constructor; eapply H.
(* here *)
inversion HT; subst.
destruct (IHM A0 EmptyCtx HT0).
left; apply val_here; assumption.
right; destruct H; exists (here x); eauto using step.
(* get_here *)
inversion HT; subst.
destruct (IHM A0 EmptyCtx).
assert (Gamma = nil).
  apply EmptyCtx with (G' := G0 & Gamma).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right;
  rewrite Mem_cons_eq; left; reflexivity.
subst. 
apply BackgroundSubsetImpl with (G:=G0 & nil).
assumption.
exists nil; permut_simpl; assumption.
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
assert (Gamma = nil).
  apply EmptyCtx with (G' := G0 & Gamma).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right;
  rewrite Mem_cons_eq; left; reflexivity.
subst.
apply BackgroundSubsetImpl with (G:=G0 & nil).
assumption.
exists nil; permut_simpl; assumption.
inversion H; subst; inversion HT1; subst.
  exists [M//0]M2; eauto using step.
  exists [M//0]M2; eauto using step.
destruct H; exists (letdia_get x M2); eauto using step.
Qed.

(* Original formulations of modified typing rules can be reconstructed *)
Lemma test_box:
  forall G G' Gamma M A,
    G & Gamma ++ G' |=  nil |- M ::: A ->
      G ++ G' |= Gamma |- box M ::: [*]A.
intros.
constructor.
apply BackgroundSubsetImpl with (G:=G & Gamma ++ G').
assumption.
exists nil; permut_simpl.
Qed.

Lemma test_unbox_fetch:
  forall G G' Gamma Gamma' M A,
    G & Gamma ++ G' |= Gamma' |- M ::: [*] A ->
      G & Gamma' ++ G' |= Gamma |- unbox_fetch M ::: A.
intros.
apply t_unbox_fetch with (G:=G ++ G') (Gamma:=Gamma').
apply BackgroundSubsetImpl with (G:=G & Gamma ++ G').
assumption.
exists nil; permut_simpl.
permut_simpl.
Qed.

Lemma test_get_here:
  forall G G' Gamma Gamma' M A,
    G & Gamma' ++ G' |= Gamma |- M ::: A ->
      G & Gamma ++ G' |= Gamma' |- get_here M ::: <*> A.
intros.
apply t_get_here with (G:=G ++ G') (Gamma:=Gamma).
apply BackgroundSubsetImpl with (G:=G & Gamma' ++ G').
assumption.
exists nil; permut_simpl.
permut_simpl.
Qed.

Lemma test_letdia_get:
  forall G G' Gamma Gamma' M N A B,
    G & Gamma' ++ G' |= Gamma |- M ::: <*>A ->
    (A::nil) :: G & Gamma ++ G' |= Gamma' |- N ::: B ->
      G & Gamma ++ G' |= Gamma' |-  letdia_get M N ::: B.
intros.
apply t_letdia_get with (A:=A) (Gamma:=Gamma) (G:=G ++ G').
apply BackgroundSubsetImpl with (G:=G & Gamma' ++ G').
  assumption.
  exists nil; permut_simpl.
apply BackgroundSubsetImpl with (G:=(A::nil) :: G & Gamma ++ G').
  assumption.  
  exists nil; permut_simpl.
permut_simpl.
Qed.

End Lemmas.

Close Scope is5_scope.