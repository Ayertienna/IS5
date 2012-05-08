(* TODO: imports are messed up now that there's a module *) 
Require Import Syntax.
Require Import Substitution.
Require Import LibList.
Require Import LibListSorted.
Require Import Arith.

Open Scope label_free_is5_scope.

Global Reserved Notation " G '|=' Gamma '|-' M ':::' A " (at level 70).

Definition Background_LF := list Context_LF.

(* Statics *)

Inductive types_LF: Background_LF -> Context_LF -> te_LF -> ty_LF -> Prop :=

| t_hyp_LF: forall A G Gamma v_n
  (HT: Nth v_n Gamma A),
  G |= Gamma |- (hyp_LF v_n) ::: A

| t_lam_LF: forall A B G Gamma M 
  (HT: G |= A::Gamma |- M ::: B),
  G |= Gamma |- (lam_LF A M) ::: A ---> B

| t_appl_LF: forall A B G Gamma M N
  (HT1: G |= Gamma |- M ::: A ---> B)
  (HT2: G |= Gamma |- N ::: A),
  G |= Gamma |- (appl_LF M N) ::: B

| t_box_LF: forall A G Gamma M
  (HT: G & Gamma |= nil |- M ::: A),
  G |= Gamma |- (box_LF M) ::: [*] A

| t_unbox_LF: forall A G Gamma M
  (HT: G |= Gamma |- M ::: [*] A),
  G |= Gamma |- unbox_LF M ::: A

| t_unbox_fetch_LF: forall A G Gamma Gamma' M
  (HT: G & Gamma' |= Gamma |- M ::: [*] A),
  forall G', permut (G & Gamma) G' ->
    G' |= Gamma' |- unbox_fetch_LF M Gamma ::: A

| t_here_LF: forall A G Gamma M
  (HT: G |= Gamma |- M ::: A),
  G |= Gamma |- here_LF M ::: <*> A

| t_get_here_LF: forall A G Gamma Gamma' M
  (HT: G & Gamma' |= Gamma |- M ::: A),
  forall G0, permut (G & Gamma) G0 -> 
    G0 |= Gamma' |- get_here_LF M Gamma ::: <*> A

| t_letdia_LF: forall A B G Gamma M N
  (HT1: G |= Gamma |- M ::: <*> A)
  (HT2: (A :: nil) :: G |= Gamma |- N ::: B),
  G |= Gamma |- letdia_LF M N ::: B 

| t_letdia_get_LF: forall A B G Gamma Gamma' M N
  (HT1: G & Gamma' |= Gamma |- M ::: <*> A)
  (HT2: (A :: nil) :: G & Gamma |= Gamma' |- N ::: B),
  forall G0, permut (G & Gamma) G0 -> 
    G0 |= Gamma' |- letdia_get_LF M N Gamma ::: B

where " G '|=' Gamma '|-' M ':::' A " := (types_LF G Gamma M A) : label_free_is5_scope.

(* Dynamics *)

Inductive value_LF: te_LF -> Prop :=
| val_lam_LF: forall A M, value_LF (lam_LF A M)
| val_box_LF: forall M, value_LF (box_LF M)
| val_here_LF: forall M, value_LF M -> value_LF (here_LF M)
| val_get_here_LF: forall M Gamma, value_LF M -> value_LF (get_here_LF M Gamma)
.

Global Reserved Notation " M |-> N " (at level 70).

Inductive step_LF: (te_LF * Context_LF * Background_LF) -> (te_LF * Context_LF * Background_LF) -> Prop :=

| red_appl_lam_LF: forall G Gamma M A N,
  (appl_LF (lam_LF A M) N, Gamma, G) |-> 
    ([N//0 | Gamma][M | Gamma], Gamma, G)

| red_unbox_box_LF: forall G Gamma M, (* ! ?added nil to G ! *)
  (unbox_LF (box_LF M), Gamma, G) |-> 
    (M, Gamma, G)

| red_unbox_fetch_box_LF: forall G Gamma Gamma' M, (* ! ?added nil to G ! *)
  (unbox_fetch_LF (box_LF M) Gamma', Gamma, G) |-> 
    (M, Gamma, G) 

| red_letdia_here_LF: forall G Gamma M N A,
  G |= Gamma |- here_LF M ::: <*>A ->
  (letdia_LF (here_LF M) N, Gamma, G) |-> 
    ([M // 0 | (A::nil)][N | Gamma], Gamma, G)

| red_letdia__get_here_LF: forall G Gamma Gamma' M N A,
  G |= Gamma |- get_here_LF M Gamma' ::: <*> A ->
  (letdia_LF (get_here_LF M Gamma') N, Gamma, G) |-> 
    ([M // 0 | (A::nil)][N | Gamma] , Gamma, G)

| red_letdia_get__here_LF: forall G G' Gamma Gamma' M N A,
  permut (G' & Gamma') (G & Gamma) ->
  G' |= Gamma' |- here_LF M ::: <*> A ->
  (letdia_get_LF (here_LF M) N Gamma', Gamma, G) |-> 
    ([M // 0 | (A::nil)][N | Gamma], Gamma, G)

| red_letdia_get_get_here_LF: forall G G' Gamma Gamma' Delta M N A,
  permut (G' & Gamma') (G & Gamma) ->
  G' |= Gamma' |- get_here_LF M Delta ::: <*> A ->
  (letdia_get_LF (get_here_LF M Delta) N Gamma', Gamma, G) |-> 
    ([M // 0 | (A::nil)][N | Gamma], Gamma, G)

| red_appl_LF: forall G Gamma M N M'
  (HT: (M, Gamma, G) |-> (M', Gamma, G)), 
  (appl_LF M N, Gamma, G) |-> (appl_LF M' N, Gamma, G)

| red_unbox_LF: forall G Gamma M M'
  (HT: (M, Gamma, G) |-> (M', Gamma, G)), 
  (unbox_LF M, Gamma, G) |-> (unbox_LF M', Gamma, G)

| red_unbox_fetch_LF: forall G G' Gamma' M M' Gamma
(*
  (HPermutG': permut G' (G & Gamma'))
  (HPermutG'': permut G'' (G & Gamma))
*)
  (HT: (M, Gamma', G') |-> (M', Gamma', G')), 
  (unbox_fetch_LF M Gamma', Gamma, G) |-> (unbox_fetch_LF M' Gamma', Gamma, G)

| red_here_LF: forall G Gamma M M' 
  (HT: (M, Gamma, G) |-> (M', Gamma, G)), 
  (here_LF M, Gamma, G) |-> (here_LF M', Gamma, G)

| red_get_here_LF: forall G  G' Gamma Gamma' M M' 
(*
  (HPermutG': permut G' (G & Gamma'))
  (HPermutG'': permut G'' (G & Gamma))
*)
  (HT: (M, Gamma, G') |-> (M', Gamma, G')), 
  (get_here_LF M Gamma, Gamma', G) |-> (get_here_LF M' Gamma, Gamma', G)

| red_letdia_LF: forall G Gamma M N M' 
  (HT: (M, Gamma, G) |-> (M', Gamma, G)),
  (letdia_LF M N, Gamma, G) |-> (letdia_LF M' N, Gamma, G)

| red_letdia_move_LF: forall G G' Gamma Gamma' M N M'
(*
  (HPermutG': permut G' (G & Gamma'))
  (HPermutG'': permut G'' (G & Gamma)) 
*)
  (HT: (M, Gamma, G') |-> (M', Gamma, G')), 
  (letdia_get_LF M N Gamma, Gamma', G) |-> (letdia_get_LF M' N Gamma, Gamma', G)

where " M |-> N " := (step_LF M N ) : label_free_is5_scope.

Section Lemmas.

(* TODO: this may be moved to a separate file *)
(* Permutation *)

(* TODO *)
Lemma PermutLastSame:
forall A G G' (elem:A),
  permut (G & elem) (G' & elem)
  <->
  permut G G'.
Admitted.

(* TODO *)
Lemma PermutationElementSplit_Neq:
forall A G G' H (elem:A) (elem':A)
  (HNeq: elem <> elem')
  (HT: permut (G & elem ++ G') (H & elem')),
  exists GH, exists GT, H = GH & elem ++ GT.
Admitted.

(* TODO: not automated enough *)
Lemma BackgroundSubsetImpl:
forall G G' Gamma M A
  (HT: G |= Gamma |- M ::: A)
  (HSubst: exists GT, permut (G++GT) G'),
  G' |= Gamma |- M ::: A.
intros;
generalize dependent G';
induction HT; intros; eauto using types_LF.
(* box *)
destruct HSubst as [GT];
constructor;
apply IHHT;
exists GT; permut_simpl; assumption.
(* unbox_fetch *)
destruct HSubst as [GT];
apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=G++GT).
apply IHHT;
  exists GT; permut_simpl.
apply permut_trans with (l2:= G' ++ GT); 
[ permut_simpl | ]; assumption.
(* get_here *)
destruct HSubst as [GT];
apply t_get_here_LF with (Gamma:=Gamma) (G:=G++GT).
apply IHHT;
  exists GT; permut_simpl.
apply permut_trans with (l2:= G0 ++ GT); 
[ permut_simpl | ]; assumption.
(* letdia *)
apply t_letdia_LF with (A:=A). 
apply IHHT1; assumption.
apply IHHT2; destruct HSubst as [GT];
exists GT; permut_simpl; assumption.
(* letdia_get *)
destruct HSubst as [GT];
apply t_letdia_get_LF with (A:=A)(Gamma:=Gamma) (G:=G++GT).
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

(* When we have e.g. unbox_fetch M' Gamma and we weaken Gamma into Gamma++Delta, 
   we need to change the term as well *)

Reserved Notation " {{ A ~> B }} M " (at level 70).  
Reserved Notation " }} A ~> B {{ [ M | C ] " (at level 70).

Fixpoint inner_term_weakening (M: te_LF) (Gamma: Context_LF) (Delta: Context_LF) :=
match M with
| hyp_LF n => hyp_LF n
| lam_LF A M' => lam_LF A ({{ Delta ~> A::Gamma}} M')
| appl_LF M' N => appl_LF ({{Delta ~> Gamma}} M') ({{Delta ~> Gamma}} N)
| box_LF M' => box_LF (}}Delta ~> Gamma{{ [ M' | nil ] )
| unbox_LF M' => unbox_LF ({{Delta ~> Gamma}} M')
| unbox_fetch_LF M' Gamma' => unbox_fetch_LF (}}Delta ~> Gamma{{ [M' | Gamma']) Gamma'
| here_LF M' => here_LF ({{Delta ~> Gamma}} M') 
| get_here_LF M' Gamma' => get_here_LF (}}Delta ~> Gamma{{ [M' | Gamma']) Gamma'
| letdia_LF M' N => letdia_LF ({{Delta ~> Gamma}} M') ({{Delta ~> Gamma}} N)
| letdia_get_LF M' N Gamma' =>
  letdia_get_LF (}}Delta ~> Gamma{{ [M' | Gamma']) ({{Delta ~> Gamma}} N) Gamma'
end
where " {{ A ~> B }} M " := (inner_term_weakening M B A)
with
outer_term_weakening  (M: te_LF) (Gamma: Context_LF) (Gamma': Context_LF) (Delta: Context_LF) :=
match M with
| hyp_LF n => hyp_LF n
| lam_LF A M' => lam_LF A (}}Delta ~> Gamma'{{ [M'| A::Gamma])
| appl_LF M' N => 
  appl_LF (}} Delta ~> Gamma'{{ [M'| Gamma]) (}}Delta ~> Gamma'{{ [N | Gamma])
| box_LF M' => box_LF (}} Delta ~> Gamma'{{ [M' | nil])
(*
  match eq_context_LF_dec Gamma' nil with
    | left _ => box_LF ({{Delta ~> nil}} M')
    | right _ => box_LF (}}Delta ~> Gamma'{{ [M' | nil])
  end
*)
| unbox_LF M' => unbox_LF (}}Delta ~> Gamma'{{ [M' | Gamma])
| unbox_fetch_LF M' Gamma'' =>
  match eq_context_LF_dec Gamma' Gamma'' with
    | left _ => unbox_fetch_LF ({{Delta ~> Gamma''}} M') (Gamma''++Delta)
    | right _ => unbox_fetch_LF (}}Delta ~> Gamma'{{ [M' | Gamma'']) Gamma''
  end
| here_LF M' => here_LF (}}Delta ~> Gamma'{{ [M' | Gamma]) 
| get_here_LF M' Gamma'' => 
  match eq_context_LF_dec Gamma' Gamma'' with
    | left _ => get_here_LF ({{Delta ~> Gamma''}} M') (Gamma''++Delta)
    | right _ => get_here_LF (}}Delta ~> Gamma'{{ [M' | Gamma'']) Gamma''
  end
| letdia_LF M' N => 
  letdia_LF (}}Delta ~> Gamma'{{ [M' | Gamma]) (}}Delta ~> Gamma'{{ [N | Gamma])
| letdia_get_LF M' N Gamma'' =>
  match eq_context_LF_dec Gamma' Gamma'' with
    | left _ => 
      letdia_get_LF ({{Delta ~> Gamma''}} M') 
                    (}}Delta ~> Gamma'{{ [N | Gamma]) (Gamma''++Delta)
    | right _ =>  
      letdia_get_LF (}}Delta ~> Gamma'{{ [M' | Gamma''])
                    (}}Delta ~> Gamma'{{ [N | Gamma]) Gamma''
  end
end
where " }} A ~> B {{ [ M | C ] " := (outer_term_weakening M C B A).

(* TODO: ugly!!!... *)
Lemma Weakening_general:
  forall G Gamma M A
  (HT: G |= Gamma |- M ::: A),
  (forall G' Delta Delta',
    permut G (G' & Delta) ->
    G' & (Delta ++ Delta') |= Gamma |- (}}Delta' ~> Delta{{ [M | Gamma]) ::: A) /\ 
  (forall Gamma',
    G |= Gamma ++ Gamma' |- ({{Gamma' ~> Gamma}}M) ::: A).
intros;
induction HT; split;
intros; subst; simpl.
(* hyp *)
eauto using types_LF.
constructor; generalize dependent v_n;
induction Gamma; destruct v_n; intros;
try (apply Nth_nil_inv in HT; contradiction);
apply Nth_app_l; assumption.
(* lam *)
constructor; eapply IHHT; eauto.
constructor; eapply IHHT; eauto.
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
destruct (eq_context_LF_dec Delta Gamma).
(* = *)
subst.
apply t_unbox_fetch_LF with (G:=G).
  apply IHHT.
  apply permut_app_l;
  apply PermutLastSame with (elem:=Gamma);
  apply permut_trans with (l2:=G'); assumption.
(* <> *)
assert (exists G0, exists G1, G'0 = G0 & Gamma ++ G1).
  apply PermutationElementSplit_Neq with (G:=G) (G':=nil) (elem':=Delta).
    intro e; symmetry in e; contradiction.
    rew_app; apply permut_trans with (l2:=G'); assumption.
destruct H1 as [GH]; destruct H1 as [GT]; subst G'0.
apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=GH ++ GT & (Delta ++ Delta')).
apply BackgroundSubsetImpl with (G:= (GH ++ GT & Gamma') & (Delta ++ Delta')).
  apply IHHT; permut_simpl.
  apply PermutLastSame with (elem := Gamma).
  apply permut_trans with (l2:=G').
    assumption.
    apply permut_trans with (l2:=(GH & Gamma ++ GT) & Delta).
      assumption.
      permut_simpl.
  exists nil; permut_simpl.
permut_simpl.
(* unbox_fetch 2 *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma).
  apply IHHT; permut_simpl.
  assumption.
(* here *)
constructor; apply IHHT; assumption.
constructor; apply IHHT; assumption.
(* get_here 1 *)
destruct (eq_context_LF_dec Delta Gamma).
(* = *)
subst;
apply t_get_here_LF with (Gamma:=Gamma++Delta') (G:=G).
  apply IHHT.
  apply permut_app_l;
  apply PermutLastSame with (elem:=Gamma);
  apply permut_trans with (l2:=G0); assumption.
(* <> *)
assert (exists G0, exists G1, G' = G0 & Gamma ++ G1).
  apply PermutationElementSplit_Neq with (G:=G) (G':=nil) (elem':=Delta).
    intro e; symmetry in e; contradiction.
    rew_app; apply permut_trans with (l2:=G0); assumption.
destruct H1 as [GH]; destruct H1 as [GT]; subst G';
apply t_get_here_LF with (Gamma:=Gamma) (G:=GH ++ GT & (Delta ++ Delta')).
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
apply t_get_here_LF with (G:=G) (Gamma:=Gamma).
  apply IHHT; permut_simpl.
  assumption.
(* letdia *)
apply t_letdia_LF with (A:=A).
apply IHHT1; assumption.
apply IHHT2 with (G':=(A::nil)::G');
permut_simpl;
assumption.
apply t_letdia_LF with (A:=A).
apply IHHT1; assumption.
apply IHHT2. 
(* letdia_get 1 *)
destruct (eq_context_LF_dec Delta Gamma).
(* = *)
subst;
apply t_letdia_get_LF with (A:=A)(Gamma:=Gamma++Delta') (G:=G).
apply IHHT1; assumption.
apply BackgroundSubsetImpl with (G:=((A::nil) :: G) & (Gamma ++ Delta')).
  apply IHHT2; permut_simpl.
  exists nil; permut_simpl.
apply permut_app_l;
apply PermutLastSame with (elem:=Gamma);
apply permut_trans with (l2:=G0); assumption.
(* <> *)
assert (exists G0, exists G1, G' = G0 & Gamma ++ G1).
  apply PermutationElementSplit_Neq with (G:=G) (G':=nil) (elem':=Delta).
    intro e; symmetry in e; contradiction.
    rew_app; apply permut_trans with (l2:=G0); assumption.
destruct H1 as [GH]; destruct H1 as [GT];
subst G';
apply t_letdia_get_LF with (A:=A)(Gamma:=Gamma) (G:=GH ++ GT & (Delta ++ Delta')).
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
apply t_letdia_get_LF with (A:=A)(G:=G) (Gamma:=Gamma).
apply IHHT1; permut_simpl.
apply IHHT2; permut_simpl.
assumption.
Qed.

Lemma WeakeningBackgroundElem:
forall G G' Delta Delta' Gamma M A
  (HT: G & Delta ++ G' |= Gamma |- M ::: A),
  G & (Delta ++ Delta') ++ G' |= Gamma |- }} Delta' ~> Delta{{ [M | Gamma] ::: A.
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
  G |= Gamma ++ Gamma' |- {{Gamma' ~> Gamma}}M ::: A.
intros;
eapply Weakening_general; eassumption.
Qed.

Lemma Progress:
forall G M A
  (EmptyCtx: forall G', 
    permut G G' -> 
    forall Ctx, Mem Ctx G' -> Ctx = nil)
  (HT: G |= nil |- M ::: A),
  value_LF M \/ exists N, (M, nil, G) |-> (N, nil, G).
induction M; intros; eauto using value_LF.
(* hyp *)
inversion HT; destruct n;
apply Nth_nil_inv in HT0; contradiction.
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
assert (c = nil).
  apply EmptyCtx with (G':=G0 & c).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right; rewrite Mem_cons_eq; left; reflexivity.
subst; destruct (IHM ([*]A) EmptyCtx).
apply BackgroundSubsetImpl with (G:=G0 & nil). 
assumption.
exists nil; rew_app; assumption.
inversion H; subst; inversion HT0; subst; eexists; constructor.
destruct H as [M'].
exists (unbox_fetch_LF M' nil). 
apply red_unbox_fetch_LF with (G':=G).
assumption.
(* here *)
inversion HT; subst.
destruct (IHM A0 EmptyCtx HT0).
left; apply val_here_LF; assumption.
right; destruct H; exists (here_LF x); eauto using step_LF.
(* get_here *)
inversion HT; subst.
assert (c = nil).
  apply EmptyCtx with (G' := G0 & c).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right;
  rewrite Mem_cons_eq; left; reflexivity.
subst; destruct (IHM A0 EmptyCtx).
apply BackgroundSubsetImpl with (G:=G0 & nil).
assumption.
exists nil; permut_simpl; assumption.
left; econstructor; eassumption.
right; destruct H as [x]; exists (get_here_LF x nil);
apply red_get_here_LF with (G':=G); assumption.
(* letdia *)
right; inversion HT; subst.
destruct (IHM1 (<*>A0) EmptyCtx HT1).
inversion H; subst; inversion HT1; subst.
  exists ([M//0 | A0::nil][M2 | nil]);
  apply red_letdia_here_LF; assumption.
  exists ([M//0 | A0::nil][M2 | nil]);
  apply red_letdia__get_here_LF; assumption.
destruct H; exists (letdia_LF x M2); eauto using step_LF.
(* letdia_get *)
right; inversion HT; subst.
assert (c = nil).
  apply EmptyCtx with (G' := G0 & c).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right;
  rewrite Mem_cons_eq; left; reflexivity.
subst; destruct (IHM1 (<*>A0) EmptyCtx).
apply BackgroundSubsetImpl with (G:=G0 & nil).
assumption.
exists nil; permut_simpl; assumption.
inversion H; subst; inversion HT1; subst.
  exists ([M//0 | A0::nil][M2 | nil]).
  apply red_letdia_get__here_LF with (G':=G0&nil).
    apply permut_app_l; assumption.
    assumption.
  exists ([M//0 | A0::nil][M2 | nil]).
  apply red_letdia_get_get_here_LF with (G':=G0&nil).
    apply permut_app_l; assumption.
    assumption.
destruct H as [x];
exists (letdia_get_LF x M2 nil); 
eauto using step_LF.
Qed.

(* Original formulations of modified typing rules can be reconstructed *)
Lemma test_box:
  forall G G' Gamma M A,
    G & Gamma ++ G' |=  nil |- M ::: A ->
      G ++ G' |= Gamma |- box_LF M ::: [*]A.
intros; constructor;
apply BackgroundSubsetImpl with (G:=G & Gamma ++ G');
[ assumption | exists nil; permut_simpl].
Qed.

Lemma test_unbox_fetch:
  forall G G' Gamma Gamma' M A,
    G & Gamma ++ G' |= Gamma' |- M ::: [*] A ->
      G & Gamma' ++ G' |= Gamma |- unbox_fetch_LF M Gamma' ::: A.
intros;
apply t_unbox_fetch_LF with (G:=G ++ G') (Gamma:=Gamma');
[apply BackgroundSubsetImpl with (G:=G & Gamma ++ G') | permut_simpl];
[ assumption | exists nil; permut_simpl].
Qed.

Lemma test_get_here:
  forall G G' Gamma Gamma' M A,
    G & Gamma' ++ G' |= Gamma |- M ::: A ->
      G & Gamma ++ G' |= Gamma' |- get_here_LF M Gamma ::: <*> A.
intros;
apply t_get_here_LF with (G:=G ++ G') (Gamma:=Gamma);
[apply BackgroundSubsetImpl with (G:=G & Gamma' ++ G') | permut_simpl];
[assumption | exists nil; permut_simpl].
Qed.

Lemma test_letdia_get:
  forall G G' Gamma Gamma' M N A B,
    G & Gamma' ++ G' |= Gamma |- M ::: <*>A ->
    (A::nil) :: G & Gamma ++ G' |= Gamma' |- N ::: B ->
      G & Gamma ++ G' |= Gamma' |-  letdia_get_LF M N Gamma ::: B.
intros;
apply t_letdia_get_LF with (A:=A) (Gamma:=Gamma) (G:=G ++ G');
[ apply BackgroundSubsetImpl with (G:=G & Gamma' ++ G') |
  apply BackgroundSubsetImpl with (G:=(A::nil) :: G & Gamma ++ G') |
  permut_simpl];
  [assumption | exists nil; permut_simpl |
   assumption | exists nil; permut_simpl ].
Qed.

End Lemmas.

Close Scope label_free_is5_scope.