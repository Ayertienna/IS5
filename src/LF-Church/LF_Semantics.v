Add LoadPath "..".
Require Export LF_Syntax.
Require Export LF_Substitution.
Require Export LF_OkLib.
Require Export LF_EmptyEquivLib.
Require Export Classes.RelationClasses.

Open Scope permut_scope.
Open Scope is5_scope.

Reserved Notation " G  '|=' Gamma '|-' M ':::' A" (at level 70).

Section UnsafeTypes.
Print ty.
Definition defaultType := tvar.
SearchAbout var.

Fixpoint apply_unsafe t1 t2 : ty :=
match t1 with
| a ---> b => if eq_ty_dec a t2 then b else defaultType
| _ => defaultType
end. 

Fixpoint unbox_unsafe t: ty :=
match t with
| [*] t' => t'
| _ => defaultType
end.

Fixpoint find_unsafe v G : ty :=
match G with
| nil => defaultType
| (x, a)::G' => if eq_var_dec x v then a else find_unsafe v G'
end.

Fixpoint nth_unsafe n L : ty :=
match L with
| nil => defaultType
| (x::xs) =>
  match n with
    | 0 => x
    | S n' => nth_unsafe n' xs
  end
end.

Fixpoint types_unsafe (G: ctx_LF) (Gamma: list ty) (M0: te_LF) : ty :=
match M0 with
| hyp_LF (bte n) => nth_unsafe n Gamma
| hyp_LF (fte v) => find_unsafe v G
| lam_LF t M => t ---> types_unsafe G (t::Gamma) M
| appl_LF M N => apply_unsafe (types_unsafe G Gamma M) (types_unsafe G Gamma N)
| box_LF M => [*] (types_unsafe G Gamma M)
| unbox_LF M => unbox_unsafe (types_unsafe G Gamma M)
| here_LF M => <*> (types_unsafe G Gamma M)
| letdia_LF t M N => 
  if (eq_ty_dec t (types_unsafe G Gamma M)) then
    types_unsafe G (t::Gamma) N
  else defaultType
end.

End UnsafeTypes.

Inductive types_LF : bg_LF -> ctx_LF -> te_LF -> ty -> Prop :=

| t_hyp_LF: forall A G Gamma v
  (Ok: ok_Bg_LF (Gamma::G))
  (H: Mem (v, A) Gamma),
  G |= Gamma |- hyp_LF (fte v) ::: A

| t_lam_LF: forall L A B G Gamma M
  (Ok: ok_Bg_LF (Gamma::G))
  (H: forall v, v \notin L ->
    G |= (v, A)::Gamma |- M ^t^ (hyp_LF (fte v)) ::: B),
  G |= Gamma |- lam_LF A M ::: A ---> B

| t_appl_LF: forall A B G Gamma M N
  (Ok: ok_Bg_LF (Gamma::G))
  (H1: G |= Gamma |- M ::: A ---> B)
  (H2: G |= Gamma |- N ::: A),
  G |= Gamma |- appl_LF M N ::: B

| t_box_LF: forall G Gamma M A
  (Ok: ok_Bg_LF (G & Gamma))
  (H: G & Gamma |= nil |- M ::: A),
  G |= Gamma |- box_LF M ::: [*] A

| t_unbox_LF: forall G Gamma M A
  (Ok: ok_Bg_LF (Gamma :: G))
  (H: G |= Gamma |- M ::: [*] A),
  G |= Gamma |- unbox_LF M ::: A

| t_unbox_fetch_LF: forall G Gamma Gamma' M A
  (Ok: ok_Bg_LF (Gamma:: G & Gamma'))
  (H: G & Gamma' |= Gamma |- M ::: [*] A),
  forall G', G & Gamma ~=~ G' ->
    G' |= Gamma' |- unbox_LF M ::: A

| t_here_LF: forall A G Gamma M
  (Ok: ok_Bg_LF (Gamma :: G))
  (H: G |= Gamma |- M ::: A),
  G |= Gamma |- here_LF M ::: <*> A

| t_get_here_LF: forall A G Gamma Gamma' M
  (Ok: ok_Bg_LF (Gamma :: G & Gamma'))
  (H: G & Gamma' |= Gamma |- M ::: A),
  forall G', G & Gamma ~=~ G' ->
    G' |= Gamma' |- here_LF M ::: <*> A

| t_letdia_LF: forall L A B G Gamma M N
  (Ok: ok_Bg_LF (Gamma :: G))
  (HT1: G |= Gamma |- M ::: <*> A)
  (HT2: forall G' v, v \notin L ->
    ((v, A) :: nil) :: G ~=~ G' ->
    G' |= Gamma |- N ^t^ (hyp_LF (fte v)) ::: B),
  G |= Gamma |- letdia_LF (<*> A) M N ::: B

| t_letdia_get_LF: forall L A B G Gamma Gamma' M N
  (Ok: ok_Bg_LF (Gamma :: G & Gamma'))
  (HT1: G & Gamma' |= Gamma |- M ::: <*> A)
  (HT2: forall v, v \notin L ->
    ((v, A) :: nil) :: G & Gamma |= Gamma' |-
      N ^t^ (hyp_LF (fte v))::: B),
  forall G0, G & Gamma ~=~ G0 ->
    G0 |= Gamma' |- letdia_LF (<*> A) M N ::: B

where " G '|=' Gamma '|-' M ':::' A" := (types_LF G Gamma M A).

Section SafeUnsafe.

Lemma Mem_find_unsafe:
forall Gamma v A , 
  Mem (v, A) Gamma -> forall Delta, ok_LF (Gamma++Delta) nil -> find_unsafe v (Gamma++Delta) = A.
induction Gamma; intros; simpl.
  rewrite Mem_nil_eq in H; contradiction.
  destruct a; rewrite Mem_cons_eq in H. 
  case_if.
  destruct H. 
    inversion H; subst; auto.
    apply Mem_split in H; destruct H as (hd, (tl, H)).
    assert False; [ | contradiction]. subst. 
    assert ((v,t)::(v,A)::hd ++ tl *=* (v, t) :: hd & (v, A) ++ tl) by permut_simpl.
    apply ok_LF_permut with (G':=( (v, t) :: (v, A) :: hd ++ tl) ++ Delta) in H0; eauto.
    inversion H0; inversion H6; subst; elim H11; apply Mem_here. rewrite H; auto.
  destruct H.    
    inversion H; subst; elim H1; auto.
    rewrite <- IHGamma with v A Delta; auto.
    rew_app in *; inversion H0; eapply ok_LF_used_weakening; eauto.
Qed.
Hint Resolve Mem_find_unsafe.

Fixpoint listSubst (L: list var) (c:nat) (M: te_LF) : te_LF :=
match L with
| nil => M
| v :: L' => listSubst L' (S c) ([hyp_LF (fte v)//bte c] M)
end.

Lemma types_unsafe_subst:
 forall M L G G',
   (forall v t, Mem (v,t) G' -> v \notin L) ->       
   types_unsafe G (map snd G') M = 
   types_unsafe (G'++ G) nil (listSubst (map fst G') 0 M).
(*
induction M; intros; simpl in *.
(* hyp *)
destruct v; simpl.
destruct n; simpl in *. case_if; auto;
[simpl; case_if; auto | destruct n; simpl; auto].
case_if; simpl; case_if; auto; rewrite notin_union in H; destruct H; apply notin_singleton in H1;
elim H1; auto.
(* lam *)
*)
Admitted.

Lemma types_unsafe_permut:
forall M G G' Gamma, ok_LF G nil -> G *=* G' -> types_unsafe G Gamma M = types_unsafe G' Gamma M.
induction M; intros; simpl in *; auto.
Admitted.

Lemma typing_unsafe:
forall G Gamma M A, G |= Gamma |- M ::: A -> types_unsafe (concat (Gamma::G)) nil M = A.
intros; induction H; simpl in *; eauto.
(* hyp *)
apply Mem_find_unsafe; auto.
(* lam *)
assert (types_unsafe (Gamma ++ concat G) (A :: nil) M = B).
   assert {x | x \notin L} by (exists (var_gen L); apply var_gen_spec);
   destruct H1 as (v, H1). replace (A::nil) with (map snd ((v,A)::nil)) by (simpl; auto).
   rewrite types_unsafe_subst with (L:=L); auto; 
   [rewrite <- H0 with v; auto | intros; simpl; rewrite Mem_cons_eq in H2; destruct H2].
   inversion H2; subst; simpl; auto. rewrite Mem_nil_eq in H2; contradiction.
rewrite <- H1; auto.
(* appl *)
rewrite IHtypes_LF1; rewrite IHtypes_LF2; simpl; case_if; auto.
(* box *)
rewrite types_unsafe_permut with (G':=concat ( nil :: G & Gamma)). 
rewrite <- IHtypes_LF; auto. (* ! *) skip. skip.
(*unbox *)
rewrite IHtypes_LF; simpl; auto.
rewrite types_unsafe_permut with (G':=concat (Gamma::G & Gamma')). 
rewrite IHtypes_LF; simpl; auto. (* ! *) skip. skip.
(* here *)
rewrite IHtypes_LF; simpl; auto.
rewrite types_unsafe_permut with (G':=concat (Gamma :: G & Gamma')). 
rewrite IHtypes_LF; simpl; auto. (* ! *) skip. skip.
(*letdia *)
rewrite IHtypes_LF; case_if. skip.
skip.
Qed.

End SafeUnsafe.

Inductive value_LF: te_LF -> Prop :=
| val_lam_LF: forall A M, value_LF (lam_LF A M)
| val_box_LF: forall M, value_LF (box_LF M)
| val_here_LF: forall M, value_LF M -> value_LF (here_LF M)
.

Reserved Notation " M |-> N " (at level 70).

Inductive step_LF: te_LF -> te_LF -> Prop :=

| red_appl_lam_LF: forall M N A,
  lc_t_n_LF 1 M -> lc_t_LF N ->
  appl_LF (lam_LF A M) N |-> [N // bte 0] M

| red_unbox_box_LF: forall M,
  lc_t_LF M ->
  unbox_LF (box_LF M)|-> M

| red_letdia_here_LF: forall M N t,
  lc_t_LF M -> lc_t_n_LF 1 N -> value_LF M ->
  letdia_LF t (here_LF M) N |-> N ^t^ M

| red_appl_LF: forall M M' N,
  lc_t_LF M -> lc_t_LF N ->
  M |-> M'->
  appl_LF M N |-> appl_LF M' N

| red_unbox_LF: forall M M',
  lc_t_LF M -> M |-> M' ->
  unbox_LF M |-> unbox_LF M'

| red_here_LF: forall M M' ,
  lc_t_LF M -> M |-> M' ->
  here_LF M |-> here_LF M'

| red_letdia_LF: forall M M' N t,
  lc_t_LF M -> lc_t_n_LF 1 N ->
  M |-> M'->
  letdia_LF t M N |-> letdia_LF t M' N

where " M |-> N " := (step_LF M N ).

Require Export Relations.

Definition steps_LF := clos_refl_trans_1n _ step_LF.

(*
Inductive steps_LF : te_LF -> te_LF -> Prop :=
| single_step_LF: forall M M', M |-> M' -> steps_LF M M'
| multi_step_LF: forall M M' M'',
  M |-> M' -> steps_LF M' M'' -> steps_LF M M''
.
*)

Lemma PPermutationG_LF:
forall G Gamma M A G',
  G |= Gamma |- M ::: A ->
  G ~=~ G' ->
  G' |= Gamma |- M ::: A.
intros; generalize dependent G'; induction H; intros; simpl in *.

constructor; [apply ok_Bg_LF_PPermut with (G:=Gamma::G)| ]; auto;
PPermut_LF_simpl.

apply t_lam_LF with (L:=L);
[apply ok_Bg_LF_PPermut with (G:=Gamma::G)| ]; auto; PPermut_LF_simpl.

apply t_appl_LF with (A:=A);
[apply ok_Bg_LF_PPermut with (G:=Gamma::G)| |]; auto; PPermut_LF_simpl.

constructor;
[apply ok_Bg_LF_PPermut with (G:=G & Gamma)|]; auto.

constructor;
[apply ok_Bg_LF_PPermut with (G:=Gamma::G)|]; auto.

apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto. rewrite H0; auto.

constructor;
[apply ok_Bg_LF_PPermut with (G:=Gamma::G)|]; auto.

apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto. rewrite H0; auto.

apply t_letdia_LF with (A:=A) (L:=L);
[apply ok_Bg_LF_PPermut with (G:=Gamma::G) | | ]; auto.
intros; apply HT2; auto. rewrite H1; auto.

apply t_letdia_get_LF with (A:=A) (L:=L) (G:=G) (Gamma:=Gamma);
[apply ok_Bg_LF_PPermut with (G:=Gamma::G & Gamma') | | | ]; auto.
rewrite <- H2; auto.
Qed.

Lemma PermutationGamma_LF:
forall G Gamma M A Gamma',
  G |= Gamma |- M ::: A ->
  Gamma *=* Gamma' ->
  G |= Gamma' |- M ::: A.
intros. generalize dependent Gamma'.
induction H; intros; simpl in *.

constructor;
[apply ok_Bg_LF_PPermut with (G:=Gamma::G) |
 apply Mem_permut with (l:=Gamma)]; auto.

apply t_lam_LF with (L:=L);
[apply ok_Bg_LF_PPermut with (G:=Gamma::G) |]; auto.

apply t_appl_LF with (A:=A);
[apply ok_Bg_LF_PPermut with (G:=Gamma::G) | |]; auto.

constructor;
[apply ok_Bg_LF_PPermut with (G:=G & Gamma) |]; auto.
apply PPermutationG_LF with (G:=G & Gamma);
auto.

constructor;
[apply ok_Bg_LF_PPermut with (G:= Gamma :: G) |]; auto.

apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma);
[apply ok_Bg_LF_PPermut with (G:= Gamma :: G & Gamma') | |]; auto.
apply PPermutationG_LF with (G:=G & Gamma'); auto.

constructor;
[apply ok_Bg_LF_PPermut with (G:= Gamma :: G) |]; auto.

apply t_get_here_LF with (G:=G) (Gamma:=Gamma);
[apply ok_Bg_LF_PPermut with (G:= Gamma :: G & Gamma') | |]; auto.
apply PPermutationG_LF with (G:=G & Gamma'); auto.

apply t_letdia_LF with (A:=A) (L:=L);
[apply ok_Bg_LF_PPermut with (G:= Gamma :: G) | |]; auto.

apply t_letdia_get_LF with (A:=A) (L:=L) (G:=G) (Gamma:=Gamma);
[apply ok_Bg_LF_PPermut with (G:= Gamma :: G & Gamma') | | |]; auto.
apply PPermutationG_LF with (G:=G & Gamma'); auto.
Qed.


Add Morphism types_LF: PPermut_LF_types.
split; intros.
eapply PermutationGamma_LF; eauto; eapply PPermutationG_LF; eauto.
apply PermutationGamma_LF with (Gamma:=y0); [ | symmetry ]; eauto;
eapply PPermutationG_LF; eauto.
Qed.

Lemma WeakeningG_LF:
forall G Gamma M A Delta,
  G |= Gamma |- M ::: A ->
  ok_Bg_LF (Gamma::Delta::G) ->
  Delta :: G |= Gamma |- M ::: A.
intros; generalize dependent Delta; induction H;
intros; simpl in *; eauto using types_LF.

apply t_lam_LF with (L:=L \u used_vars_ctx_LF (Gamma:: Delta :: G));
auto; intros;
apply H0; auto; apply ok_Bg_LF_fresh; auto;
apply notin_Mem; rewrite notin_union in H2; destruct H2; auto.

constructor;
[apply ok_Bg_LF_PPermut with (G:=Gamma::Delta::G) | rew_app ];
auto. rew_app; PPermut_LF_simpl. apply IHtypes_LF; apply ok_Bg_LF_nil;
apply ok_Bg_LF_PPermut with (G:=Gamma::Delta::G); auto. PPermut_LF_simpl.

apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=Delta :: G);
[apply ok_Bg_LF_PPermut with (G:=Gamma'::Delta::G') | |]; auto;
rew_app. rewrite <- H0; PPermut_LF_simpl.
apply IHtypes_LF; eapply ok_Bg_LF_PPermut; eauto.
rewrite <- H0; PPermut_LF_simpl. rewrite H0; auto.

apply t_get_here_LF with (Gamma:=Gamma) (G:=Delta :: G);
[apply ok_Bg_LF_PPermut with (G:=Gamma'::Delta::G') | |]; auto.
rewrite <- H0; rew_app; PPermut_LF_simpl.
rew_app; apply IHtypes_LF; eapply ok_Bg_LF_PPermut; eauto.
rewrite <- H0; PPermut_LF_simpl.
rewrite <- H0; PPermut_LF_simpl.

apply t_letdia_LF with
  (L:=L \u used_vars_ctx_LF (Gamma :: Delta :: G)) (A:=A);
auto; intros.
apply PPermutationG_LF with (G:=Delta :: ((v, A)::nil) :: G).
apply H0; auto.
apply ok_Bg_LF_PPermut with (G:=((v,A)::nil) :: Gamma :: Delta :: G).
apply ok_Bg_LF_fresh; [apply ok_Bg_LF_nil | ]; auto.
unfold used_vars_ctx_LF in *; rew_concat in *; eauto.
PPermut_LF_simpl. rewrite <- H3; PPermut_LF_simpl.

apply t_letdia_get_LF with
  (L:=L \u from_list (map fst (Gamma' ++ Delta ++ concat G0)))
  (A:=A) (G:=Delta::G) (Gamma:=Gamma);
[apply ok_Bg_LF_PPermut with (G:=Gamma'::Delta::G0) | | |]; auto.
rewrite <- H1; PPermut_LF_simpl.
apply IHtypes_LF;
apply ok_Bg_LF_PPermut with (G:=Gamma'::Delta::G0); auto.
rewrite <- H1; PPermut_LF_simpl.
intros; apply PPermutationG_LF with (G:=Delta :: ((v, A) :: nil) :: G & Gamma).
apply H0; auto.
apply ok_Bg_LF_PPermut with (G:= ((v, A)::nil) :: Gamma' :: Delta :: G0).
apply ok_Bg_LF_fresh; [apply ok_Bg_LF_nil | ]; auto.
unfold used_vars_ctx_LF in *; rew_concat in *; eauto.
rewrite notin_union in H3; destruct H3; auto.
rewrite H1; PPermut_LF_simpl.
rew_app; PPermut_LF_simpl.
rewrite <- H1; PPermut_LF_simpl.
Qed.

Lemma WeakeningWithinContext_LF:
forall G Gamma M A,
  G |= Gamma |- M ::: A ->
  (forall Delta Delta' G',
    G' & Delta ~=~ G ->
    ok_Bg_LF (Gamma :: G' & (Delta ++ Delta')) ->
    G' & (Delta++Delta') |= Gamma |- M ::: A)
  /\
  (forall Gamma',
    ok_Bg_LF ((Gamma++Gamma')::G) ->
    G |= Gamma ++ Gamma' |- M ::: A).
intros G Gamma M A H;
induction H; split; intros; subst.
constructor; auto.
constructor; auto; rewrite Mem_app_or_eq; left; auto.
apply t_lam_LF with
  (L:=L \u
    (used_vars_ctx_LF (Gamma :: G' & (Delta ++ Delta'))));
auto; intros; eapply H0; eauto;
rew_app; apply ok_Bg_LF_fresh; eauto; apply notin_Mem;
rewrite notin_union in H3; destruct H3; auto.
apply t_lam_LF with
  (L:=L \u
    (used_vars_ctx_LF ((Gamma ++ Gamma') :: G)));
auto; intros; eapply H0; eauto;
rew_app; apply ok_Bg_LF_fresh; eauto;
rewrite notin_union in H2; destruct H2; auto.
econstructor; eauto; [eapply IHtypes_LF1 | eapply IHtypes_LF2]; eauto.
econstructor; eauto; [eapply IHtypes_LF1 | eapply IHtypes_LF2]; eauto.
econstructor;
[apply ok_Bg_LF_PPermut with (G:=Gamma:: G' & (Delta++Delta')) | ];
auto. PPermut_LF_simpl.
apply PPermutationG_LF with (G:= ((G'& Gamma) & (Delta ++ Delta'))).
eapply IHtypes_LF. rewrite <- H0; PPermut_LF_simpl.
apply ok_Bg_LF_nil; apply ok_Bg_LF_PPermut
  with (G:=Gamma :: G' & (Delta ++ Delta'));
auto. PPermut_LF_simpl.
econstructor;
[apply ok_Bg_LF_PPermut with (G:=(Gamma++Gamma'):: G) | ];
auto. PPermut_LF_simpl.
eapply IHtypes_LF; auto.
apply ok_Bg_LF_nil; apply ok_Bg_LF_PPermut with (G:=(Gamma++Gamma') :: G);
auto. PPermut_LF_simpl.
constructor; eauto; eapply IHtypes_LF; eauto.
constructor; eauto; eapply IHtypes_LF; eauto.
assert (Delta::G'0 ~=~ G & Gamma).
  transitivity G'; auto; rewrite <- H1; PPermut_LF_simpl.
assert ({Gamma *=* Delta} + {~ Gamma *=* Delta}).
  eapply permut_dec; intros; destruct k; destruct k'; repeat decide equality.
  apply eq_var_dec.
destruct H4.
(* Gamma *=* Delta *)
assert (G'0 ~=~ G).
  apply PPermut_LF_last_rev with (Gamma:=Delta) (Gamma':=Gamma).
  symmetry; auto.
  rewrite <- H3; PPermut_LF_simpl.
apply t_unbox_fetch_LF with (G:=G'0) (Gamma:=Delta++Delta'); auto.
apply ok_Bg_LF_PPermut with (G:=Gamma'::G'0&(Delta++Delta')); auto.
apply PPermutationG_LF with (G:=G & Gamma'); auto.
apply PermutationGamma_LF with (Gamma:=Gamma++Delta'); auto.
eapply IHtypes_LF.
apply ok_Bg_LF_PPermut with (G:=Gamma'::G'0&(Delta++Delta')); auto.
rewrite H4; PPermut_LF_simpl.
(* ~ Gamma *=* Delta *)
assert (G'0 & Delta ~=~ G & Gamma) by (rewrite <- H3; PPermut_LF_simpl).
apply PPermut_LF_split_neq in H4; [ | intro; elim n; symmetry; auto];
destruct H4 as (Gamma0, (hd, (tl, (H4, H5)))).
subst.
apply t_unbox_fetch_LF with (G:=hd++tl & (Delta++Delta')) (Gamma:=Gamma).
apply ok_Bg_LF_PPermut
  with (G:=Gamma' :: (hd & Gamma0 ++ tl) & (Delta ++ Delta'));
auto; rew_app; PPermut_LF_simpl.
apply PPermutationG_LF with (G:=(hd& Gamma' ++ tl) & (Delta ++ Delta')).
eapply IHtypes_LF. rew_app; PPermut_LF_simpl.
apply PPermut_LF_last_rev with (Gamma:=Gamma0) (Gamma':=Gamma); auto;
rewrite <- H3; PPermut_LF_simpl.
apply ok_Bg_LF_PPermut
  with (G:=Gamma' :: (hd & Gamma0 ++ tl) & (Delta ++ Delta'));
auto; rew_app; PPermut_LF_simpl.
rew_app; PPermut_LF_simpl.
rew_app; PPermut_LF_simpl.
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma);
[apply ok_Bg_LF_PPermut with (G:=(Gamma'++Gamma'0):: G') | | ];
auto. rewrite <- H0; PPermut_LF_simpl.
eapply IHtypes_LF; auto.
apply ok_Bg_LF_PPermut with (G:=(Gamma'++Gamma'0):: G'); auto.
rewrite <- H0; PPermut_LF_simpl.
constructor; eauto; eapply IHtypes_LF; eauto.
constructor; eauto; eapply IHtypes_LF; eauto.
assert (G & Gamma ~=~ G'0 & Delta) by (rewrite  H1; auto).
assert ({Gamma *=* Delta} + {~ Gamma *=* Delta}).
  eapply permut_dec; intros; destruct k; destruct k'; repeat decide equality;
  apply eq_var_dec.
destruct H4.
(* Gamma *=* Delta *)
assert (G'0 ~=~ G).
  apply PPermut_LF_last_rev with (Gamma:=Delta) (Gamma':=Gamma).
  symmetry; auto.
  rewrite <- H3; PPermut_LF_simpl.
apply t_get_here_LF with (G:=G'0) (Gamma:=Delta++Delta'); auto.
apply ok_Bg_LF_PPermut with (G:=Gamma'::G'0&(Delta++Delta')); auto.
apply PPermutationG_LF with (G:=G & Gamma'); auto.
apply PermutationGamma_LF with (Gamma:=Gamma++Delta'); auto.
eapply IHtypes_LF.
apply ok_Bg_LF_PPermut with (G:=Gamma'::G'0&(Delta++Delta')); auto.
rewrite H4; PPermut_LF_simpl.
(* ~ Gamma *=* Delta *)
assert (G'0 & Delta ~=~ G & Gamma) by (rewrite <- H3; PPermut_LF_simpl).
apply PPermut_LF_split_neq in H4; [ | intro; elim n; symmetry; auto];
destruct H4 as (Gamma0, (hd, (tl, (H4, H5)))).
subst.
apply t_get_here_LF with (G:=hd++tl & (Delta++Delta')) (Gamma:=Gamma).
apply ok_Bg_LF_PPermut
  with (G:=Gamma' :: (hd & Gamma0 ++ tl) & (Delta ++ Delta'));
auto; rew_app; PPermut_LF_simpl.
apply PPermutationG_LF with (G:=(hd& Gamma' ++ tl) & (Delta ++ Delta')).
eapply IHtypes_LF. rew_app; PPermut_LF_simpl.
apply PPermut_LF_last_rev with (Gamma:=Gamma0) (Gamma':=Gamma); auto.
rewrite H3; PPermut_LF_simpl.
apply ok_Bg_LF_PPermut
  with (G:=Gamma' :: (hd & Gamma0 ++ tl) & (Delta ++ Delta'));
auto; rew_app; PPermut_LF_simpl.
rew_app; PPermut_LF_simpl.
rew_app; PPermut_LF_simpl.
apply t_get_here_LF with (G:=G) (Gamma:=Gamma);
[apply ok_Bg_LF_PPermut with (G:=(Gamma'++Gamma'0):: G') | | ];
auto. rewrite <- H0; PPermut_LF_simpl.
eapply IHtypes_LF. auto.
apply ok_Bg_LF_PPermut with (G:=(Gamma'++Gamma'0):: G'); auto. rewrite <- H0;
PPermut_LF_simpl.
apply t_letdia_LF with (A:=A)
  (L:=L \u (used_vars_ctx_LF (Gamma :: G' & (Delta ++ Delta'))));
auto; [apply IHtypes_LF | intros]; auto.
apply PPermutationG_LF with (G:= (((v, A) :: nil) :: G') & (Delta ++ Delta')).
eapply H0 with (G':=((v, A)::nil) :: G' & Delta).
auto. rewrite H1; rew_app; PPermut_LF_simpl. rew_app; PPermut_LF_simpl.
apply ok_Bg_LF_PPermut
  with (G:=((v, A) :: nil) :: Gamma :: G' & (Delta ++Delta')).
apply ok_Bg_LF_fresh. apply ok_Bg_LF_nil; auto.
unfold used_vars_ctx_LF in *; rew_concat in *; eauto.
rew_app; PPermut_LF_simpl.
rew_app; auto.
apply t_letdia_LF with (A:=A)
  (L:=L \u (used_vars_ctx_LF ((Gamma++Gamma') :: G)));
auto; [apply IHtypes_LF | intros]; auto.
eapply H0; eauto.
apply ok_Bg_LF_PPermut with (G:=((v, A) :: nil) :: (Gamma++Gamma') :: G).
apply ok_Bg_LF_fresh. apply ok_Bg_LF_nil; auto.
unfold used_vars_ctx_LF in *; rew_concat in *; eauto.
rewrite <- H3; PPermut_LF_simpl.
assert (Gamma::G ~=~ G' & Delta).
  transitivity G0; auto; rewrite <- H1; PPermut_LF_simpl.
assert ({Gamma *=* Delta} + {~ Gamma *=* Delta}).
  eapply permut_dec; intros; destruct k; destruct k'; repeat decide equality.
  apply eq_var_dec.
destruct H5.
(* Gamma *=* Delta *)
assert (G ~=~ G').
  apply PPermut_LF_last_rev with (Gamma:=Gamma) (Gamma':=Delta).
  auto.
  rewrite <- H4; PPermut_LF_simpl.
apply t_letdia_get_LF with (A:=A)
(L:=L \u used_vars_ctx_LF (nil :: Gamma' :: G' & (Delta ++ Delta'))) (G:=G')
(Gamma:=Delta++Delta'); auto.
apply ok_Bg_LF_PPermut with (G:=Gamma'::G'&(Delta++Delta')); auto.
apply PPermutationG_LF with (G:=G & Gamma'); auto.
apply PermutationGamma_LF with (Gamma:=Gamma++Delta'); auto.
eapply IHtypes_LF.
apply ok_Bg_LF_PPermut with (G:=Gamma'::G'&(Delta++Delta')); auto.
rewrite H5; PPermut_LF_simpl.
intros; destruct H0 with (v:=v); auto.
apply PPermutationG_LF with (G:=((((v, A) :: nil) :: G') & (Delta ++ Delta'))).
eapply H7. rewrite H5; PPermut_LF_simpl.
apply ok_Bg_LF_PPermut with (G:=((v,A)::nil)::Gamma' :: G' & (Delta ++ Delta')).
apply ok_Bg_LF_fresh. auto. rewrite notin_union in H6; destruct H6. auto.
PPermut_LF_simpl. PPermut_LF_simpl.
(* ~ Gamma *=* Delta *)
assert (G' & Delta ~=~ G & Gamma) by (rewrite <- H4; PPermut_LF_simpl).
apply PPermut_LF_split_neq in H5; [ | intro; elim n; symmetry; auto];
destruct H5 as (Gamma0, (hd, (tl, (H5, H6)))).
subst.
apply t_letdia_get_LF with (G:=hd++tl & (Delta++Delta')) (Gamma:=Gamma)
 (L:=L \u used_vars_ctx_LF
     (nil :: Gamma' :: (hd & Gamma0 ++ tl) & (Delta ++ Delta'))) (A:=A).
apply ok_Bg_LF_PPermut
  with (G:=Gamma' :: (hd & Gamma0 ++ tl) & (Delta ++ Delta'));
auto; rew_app; PPermut_LF_simpl.
apply PPermutationG_LF with (G:=(hd& Gamma' ++ tl) & (Delta ++ Delta')).
eapply IHtypes_LF. rew_app; PPermut_LF_simpl.
apply PPermut_LF_last_rev with (Gamma:=Gamma0) (Gamma':=Gamma); auto.
transitivity (Gamma::G); auto. rewrite H4; PPermut_LF_simpl. PPermut_LF_simpl.
apply ok_Bg_LF_PPermut
  with (G:=Gamma' :: (hd & Gamma0 ++ tl) & (Delta ++ Delta'));
auto; rew_app; PPermut_LF_simpl.
rew_app; PPermut_LF_simpl.
intros; destruct H0 with (v:=v); auto.
apply PPermutationG_LF with (G:=((((v, A) :: nil) :: Gamma0:: hd++tl) &
  (Delta ++ Delta'))).
eapply H7. PPermut_LF_simpl; transitivity (Gamma::G); auto.
rewrite H4; PPermut_LF_simpl. PPermut_LF_simpl.
apply ok_Bg_LF_PPermut with (G:=((v,A)::nil)::Gamma' ::
  (hd & Gamma0 ++ tl) & (Delta ++ Delta')).
apply ok_Bg_LF_fresh. auto. rewrite notin_union in H6; destruct H6. auto.
rew_app; PPermut_LF_simpl. rew_app; PPermut_LF_simpl.
rew_app; PPermut_LF_simpl.
apply t_letdia_get_LF with (A:=A) (G:=G) (Gamma:=Gamma)
  (L:=L \u (used_vars_ctx_LF ((Gamma' ++ Gamma'0) :: G0)));
[apply ok_Bg_LF_PPermut with (G:=(Gamma'++Gamma'0):: G0) | | | ];
auto.  rewrite <- H1; PPermut_LF_simpl.
eapply IHtypes_LF. auto.
apply ok_Bg_LF_PPermut with (G:=(Gamma'++Gamma'0):: G0); auto. rewrite <- H1;
PPermut_LF_simpl.
intros. eapply H0; eauto.
apply ok_Bg_LF_PPermut with (G:=((v,A)::nil) :: (Gamma'++Gamma'0) :: G0).
apply ok_Bg_LF_fresh. apply ok_Bg_LF_nil; auto.
unfold used_vars_ctx_LF in *; rew_concat in *; eauto.
rewrite <- H1; PPermut_LF_simpl.
Qed.

Lemma WeakeningGamma_LF:
forall G Gamma M A Gamma',
  G |= Gamma |- M ::: A ->
  ok_Bg_LF ((Gamma++Gamma')::G) ->
  G |= Gamma ++ Gamma' |- M ::: A.
intros; eapply WeakeningWithinContext_LF; eauto.
Qed.

Lemma WeakeningWithinG:
forall G Gamma M A Delta Delta',
  G & Delta |= Gamma |- M ::: A ->
  ok_Bg_LF (Gamma :: G & (Delta ++ Delta')) ->
  G & (Delta++Delta')|= Gamma |- M ::: A.
intros; eapply WeakeningWithinContext_LF; eauto.
Qed.

Lemma types_weakened_LF:
forall G G' Gamma M A
  (Ok: ok_Bg_LF (Gamma::G ++ G'))
  (HT: emptyEquiv_LF G ++ G' |= nil |- M ::: A),
  G ++ G'|= Gamma |- M ::: A.
induction G; intros; simpl in *; rew_app in *; auto.
apply WeakeningGamma_LF with (Gamma':=Gamma) in HT; rew_app in *; auto.
assert (a :: G ++ G' ~=~ G ++ a::G') by PPermut_LF_simpl.
apply PPermutationG_LF with (G:=G ++ a:: G'); auto; apply IHG.
apply ok_Bg_LF_PPermut with (G:=Gamma :: a :: G ++ G'); auto.
assert (emptyEquiv_LF G ++ a :: G' ~=~
  (emptyEquiv_LF G ++ G') & (nil ++ a)).
  PPermut_LF_simpl.
apply PPermutationG_LF with (G:=(emptyEquiv_LF G  ++ G') & (nil ++ a)); auto.
eapply WeakeningWithinG.
rew_app.
apply ok_Bg_LF_empty_first in Ok.
assert (nil :: a :: G ++ G' ~=~ (nil :: G) ++ a :: G') by
  PPermut_LF_simpl.
apply ok_Bg_LF_PPermut with (G':=(nil::G)++ a::G') in Ok; auto.
eapply emptyEquiv_LF_ok_Bg_part in Ok; simpl in *; rew_app in *; auto.
assert (emptyEquiv_LF G & nil ++ G' ~=~  nil :: emptyEquiv_LF G ++ G') by
  PPermut_LF_simpl.
apply PPermutationG_LF with (G:= nil::emptyEquiv_LF G ++ G'); auto.
PPermut_LF_simpl.
apply ok_Bg_LF_nil. rew_app. apply emptyEquiv_LF_ok_Bg_part.
apply ok_Bg_LF_PPermut with (a::G ++ G');
try PPermut_LF_simpl.
eapply ok_Bg_LF_weakening; eauto.
Qed.

Lemma subst_t_LF_preserv_types:
forall G Gamma B M N v A
  (H_lc_t: lc_t_LF M)
  (HT: G |= Gamma |- N ::: B),
  (* "inner" substitution *)
  ( forall Gamma0,
    Gamma *=* ((v, A) :: Gamma0) ->
    emptyEquiv_LF G |= nil |- M ::: A ->
    G |= Gamma0 |- [M // fte v] N ::: B)
  /\
  (* "outer" substitution *)
  ( forall G0 G' G'' Gamma',
    G ~=~ (G0 & ((v,A)::Gamma')) ->
    G' ~=~ (G0 & Gamma) ->
    G'' ~=~ (G0 & Gamma') ->
    emptyEquiv_LF G' |= nil |- M ::: A ->
    G'' |= Gamma |- [M // fte v] N ::: B).
intros.
generalize dependent v;
generalize dependent A;
generalize dependent M.
induction HT; split; intros;
simpl in *.

(* hyp *)
case_if.
inversion H2; subst.
assert (A = A0) by (eapply ok_Bg_LF_Mem_eq; eauto);
subst; replace G with (G ++ nil) by (rew_app; auto).
apply types_weakened_LF.
apply ok_Bg_LF_permut_first_tail with (C':=Gamma0)(x:=v)(A:=A0) in Ok;
auto; rew_app; auto. rew_app; auto.

constructor.
apply ok_Bg_LF_permut_first_tail with (C':=Gamma0) (x:=v0) (A:=A0) in Ok; eauto.
apply Mem_permut with (l' := (v0, A0) :: Gamma0) in H; eauto;
rewrite Mem_cons_eq in H; destruct H; auto.
inversion H; subst; elim H2; reflexivity.


case_if.
inversion H4; subst.
apply ok_Bg_LF_Mem_contradict with (v:=v) (A:=A) (A':=A0) (G':=G0) (C':=Gamma')
  in Ok; rew_app in *;
contradiction || eauto.
constructor; auto.
apply ok_Bg_LF_PPermut with (G:=(Gamma::G0) & Gamma').
apply ok_Bg_LF_PPermut with (G':=(Gamma::G0 & ((v0, A0)::Gamma'))) in Ok.
apply ok_Bg_LF_permut_no_last with (v:=v0)(A:=A0); auto.
rewrite H0; PPermut_LF_simpl.
rewrite H2; PPermut_LF_simpl.

(* lam *)
apply t_lam_LF with (L:=L \u \{v}).
apply ok_Bg_LF_permut_first_tail with (C:=Gamma) (x:=v) (A:=A0); auto.
intros.
rewrite notin_union in H3; rewrite notin_singleton in H3; destruct H3.
unfold open_LF in *;
rewrite <- subst_t_comm_LF; auto.
eapply H0; auto;
permut_simpl || rew_app; eauto.

apply t_lam_LF with (L:=L \u \{v}).
apply ok_Bg_LF_PPermut with (G':=Gamma::G0 & ((v,A0)::Gamma')) in Ok.
apply ok_Bg_LF_PPermut with (G:=(Gamma::G0) & Gamma').
apply ok_Bg_LF_permut_no_last with (v:=v) (A:=A0); rew_app; auto.
rewrite H3; auto. rewrite H1; auto.
intros.
rewrite notin_union in H5; rewrite notin_singleton in H5; destruct H5;
unfold open_LF in *;
rewrite <- subst_t_comm_LF; auto.
eapply H0 with (G0:=G0); eauto;
assert (emptyEquiv_LF G' ~=~
  emptyEquiv_LF (G0 ++ nil & ((v0, A) :: Gamma))).

 (rewrite H2; rew_app; eapply emptyEquiv_LF_last_change; auto).
rew_app in *.
apply PPermutationG_LF with (G:=emptyEquiv_LF G'); auto.

(* appl *)
econstructor;  [ | eapply IHHT1 | eapply IHHT2]; eauto.
apply ok_Bg_LF_permut_first_tail with (C':=Gamma0) (x:=v) (A:=A0) in Ok; eauto.

econstructor.
apply ok_Bg_LF_PPermut with (G:=Gamma:: G0 & Gamma'); auto.
apply ok_Bg_LF_PPermut with (G':=Gamma :: G0 & ((v,A0)::Gamma')) in Ok; auto.

apply ok_Bg_LF_permut_no_last_spec in Ok; rew_app; auto.
eapply IHHT1; eauto.
eapply IHHT2; eauto.

(* box *)
constructor.
apply ok_Bg_LF_permut_no_last with (v:=v) (A:=A0);
apply ok_Bg_LF_PPermut with (G:=G & Gamma); auto.
eapply IHHT; eauto.
rewrite emptyEquiv_LF_rewrite; rewrite emptyEquiv_LF_rewrite_last;
simpl; rew_app. apply PPermutationG_LF with (nil :: emptyEquiv_LF G).
apply WeakeningG_LF; auto.

repeat apply ok_Bg_LF_nil. apply ok_Bg_LF_emptyEquiv.
PPermut_LF_simpl.

constructor.

apply ok_Bg_LF_PPermut with (G:=G0 & Gamma & Gamma').
apply ok_Bg_LF_permut_no_last with (v:=v) (A:=A0).
apply ok_Bg_LF_PPermut with (G:=G & Gamma); auto.
rewrite H; PPermut_LF_simpl.
rewrite H1; PPermut_LF_simpl.
eapply IHHT with (G0:=G0 & Gamma) (Gamma':=Gamma'); auto.
rewrite H; PPermut_LF_simpl; eauto.
rewrite H1; PPermut_LF_simpl.
repeat rewrite emptyEquiv_LF_rewrite;
simpl; rew_app.
apply PPermutationG_LF with (G:=nil::emptyEquiv_LF G').
apply WeakeningG_LF; auto.
repeat apply ok_Bg_LF_nil; apply ok_Bg_LF_emptyEquiv.
rewrite H0; rewrite emptyEquiv_LF_rewrite_last; simpl;
PPermut_LF_simpl.

(* unbox *)
econstructor; [ | eapply IHHT]; eauto;
apply ok_Bg_LF_permut_first_tail with (C':=Gamma0) (x:=v) (A:=A0) in Ok; eauto.

econstructor.
apply ok_Bg_LF_PPermut with (G:=G0 & Gamma & Gamma').
apply ok_Bg_LF_permut_no_last with (v:=v) (A:=A0).
apply ok_Bg_LF_PPermut with (G:=Gamma :: G); auto.
rewrite H; PPermut_LF_simpl.
rewrite H1; PPermut_LF_simpl.
eapply IHHT; eauto.

(* unbox_fetch *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto;
[ apply ok_Bg_LF_permut_no_last_spec with (v:=v) (A:=A0);
  apply ok_Bg_LF_PPermut with (G:= Gamma :: G & Gamma') |
  eapply IHHT; eauto]; auto.
rewrite emptyEquiv_LF_rewrite; simpl.
apply PPermutationG_LF with (emptyEquiv_LF G'); auto.
rewrite <- H; rewrite emptyEquiv_LF_rewrite; simpl; auto.

destruct (permut_dec (var * ty) Gamma ((v,A0)::Gamma'0)).
  intros; destruct k; destruct k'; repeat decide equality.
  apply eq_var_dec.
(* = *)
assert (G ~=~ G0).
  apply PPermut_LF_last_rev with (Gamma:=Gamma)(Gamma':=(v,A0)::Gamma'0);
  auto.
  transitivity G'; auto.
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma'0).
apply ok_Bg_LF_PPermut with (Gamma' :: G & Gamma'0).
apply ok_Bg_LF_permut_no_last_spec with (v:=v)(A:=A0).
apply ok_Bg_LF_PPermut with (Gamma :: G & Gamma').
auto. transitivity (((v,A0)::Gamma'0):: G & Gamma'); auto.
PPermut_LF_simpl. rew_app. transitivity (Gamma' :: Gamma'0 :: G);
PPermut_LF_simpl; auto. transitivity (Gamma'0 :: Gamma' :: G);
rew_app; PPermut_LF_simpl; auto. rew_app. constructor; auto.
PPermut_LF_simpl.
destruct IHHT with (M0:=M0) (A0:=A0) (v:=v); auto.
apply H5; auto. apply PPermutationG_LF with (G:=emptyEquiv_LF G'0);
auto. rewrite H1; rewrite H4; auto.
symmetry; rewrite H4; auto.
(* <> *)
assert (exists Gamma'', exists GH, exists GT,
  Gamma'' *=* (v, A0)::Gamma'0 /\ G = GH & Gamma'' ++ GT) as HP.
  apply PPermut_LF_split_neq with (Gamma:=Gamma) (G':=G0);
    auto; transitivity G'; auto.
destruct HP as (Gamma'', (GH, (GT, (HPa, HPb)))).
assert (GH & Gamma'' ++ GT ~=~ GH & ((v, A0)::Gamma'0) ++ GT)
  by PPermut_LF_simpl;
apply t_unbox_fetch_LF with (G:=GH ++ GT & (Gamma'0)) (Gamma:=Gamma).
subst;
apply ok_Bg_LF_PPermut with
  (G:= (((Gamma) :: (GH & (Gamma') ++ GT)) & (Gamma'0))).
apply ok_Bg_LF_permut_no_last_spec with (v:=v)(A:=A0).
apply ok_Bg_LF_PPermut with
  (G:=(Gamma):: (GH & (Gamma'') ++ GT) & (Gamma')); auto.
constructor; auto. PPermut_LF_simpl.
PPermut_LF_simpl.
destruct IHHT with (M0:=M0) (A0:=A0) (v:= v); auto.
eapply H6 with (Gamma'0:=Gamma'0) (G0:=GH ++ GT & Gamma')
  (G':=GH ++ GT & Gamma' & Gamma);subst; try PPermut_LF_simpl.
clear H5 H6 IHHT.
assert (GH ++ Gamma'' :: GT & Gamma ~=~ G0 & Gamma'').
  transitivity G'; rew_app in *; auto; rewrite H0; auto.
assert (GH ++ GT & Gamma ~=~ G0).
  apply PPermut_LF_last_rev_simpl with (a:=Gamma'');
    rewrite <- H5; PPermut_LF_simpl.
apply PPermutationG_LF with (G := emptyEquiv_LF G'0); auto.
rewrite H1; rewrite <- H6; repeat rewrite emptyEquiv_LF_rewrite;
PPermut_LF_simpl.
rewrite H2.
rew_app; PPermut_LF_simpl; apply PPermut_LF_last_rev_simpl
  with (a:=(v,A0)::Gamma'0). rewrite <- H0; rewrite <- H; subst;
  PPermut_LF_simpl.

(* here *)
econstructor; [ | eapply IHHT]; eauto;
apply ok_Bg_LF_permut_first_tail with (C':=Gamma0) (x:=v) (A:=A0) in Ok; eauto.

econstructor.
apply ok_Bg_LF_PPermut with (G:=G0 & Gamma & Gamma').
apply ok_Bg_LF_permut_no_last with (v:=v) (A:=A0).
apply ok_Bg_LF_PPermut with (G:=Gamma :: G); auto.
rewrite H; PPermut_LF_simpl.
rewrite H1; PPermut_LF_simpl.
eapply IHHT; eauto.

(* get_here *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto;
[ apply ok_Bg_LF_permut_no_last_spec with (v:=v) (A:=A0);
  apply ok_Bg_LF_PPermut with (G:= Gamma :: G & Gamma') |
  eapply IHHT; eauto]; auto.
rewrite emptyEquiv_LF_rewrite; simpl.
apply PPermutationG_LF with (emptyEquiv_LF G'); auto.
rewrite <- H; rewrite emptyEquiv_LF_rewrite; simpl; auto.

destruct (permut_dec (var * ty) Gamma ((v,A0)::Gamma'0)).
  intros; destruct k; destruct k'; repeat decide equality.
  apply eq_var_dec.
(* = *)
assert (G ~=~ G0).
  apply PPermut_LF_last_rev with (Gamma:=Gamma)(Gamma':=(v,A0)::Gamma'0);
  auto.
  transitivity G'; auto.
apply t_get_here_LF with (G:=G) (Gamma:=Gamma'0).
apply ok_Bg_LF_PPermut with (Gamma' :: G & Gamma'0).
apply ok_Bg_LF_permut_no_last_spec with (v:=v)(A:=A0).
apply ok_Bg_LF_PPermut with (Gamma :: G & Gamma').
auto. transitivity (((v,A0)::Gamma'0):: G & Gamma'); auto.
PPermut_LF_simpl. rew_app. transitivity (Gamma' :: Gamma'0 :: G);
PPermut_LF_simpl; auto. transitivity (Gamma'0 :: Gamma' :: G);
rew_app; PPermut_LF_simpl; auto. rew_app. constructor; auto.
PPermut_LF_simpl.
destruct IHHT with (M0:=M0) (A0:=A0) (v:=v); auto.
apply H5; auto. apply PPermutationG_LF with (G:=emptyEquiv_LF G'0);
auto. rewrite H1; rewrite H4; auto.
symmetry; rewrite H4; auto.
(* <> *)
assert (exists Gamma'', exists GH, exists GT,
  Gamma'' *=* (v, A0)::Gamma'0 /\ G = GH & Gamma'' ++ GT) as HP.
  apply PPermut_LF_split_neq with (Gamma:=Gamma) (G':=G0);
    auto; transitivity G'; auto.
destruct HP as (Gamma'', (GH, (GT, (HPa, HPb)))).
assert (GH & Gamma'' ++ GT ~=~ GH & ((v, A0)::Gamma'0) ++ GT)
  by PPermut_LF_simpl;
apply t_get_here_LF with (G:=GH ++ GT & (Gamma'0)) (Gamma:=Gamma).
subst;
apply ok_Bg_LF_PPermut with
  (G:= (((Gamma) :: (GH & (Gamma') ++ GT)) & (Gamma'0))).
apply ok_Bg_LF_permut_no_last_spec with (v:=v)(A:=A0).
apply ok_Bg_LF_PPermut with
  (G:=(Gamma):: (GH & (Gamma'') ++ GT) & (Gamma')); auto.
constructor; auto. PPermut_LF_simpl.
PPermut_LF_simpl.
destruct IHHT with (M0:=M0) (A0:=A0) (v:= v); auto.
eapply H6 with (Gamma'0:=Gamma'0) (G0:=GH ++ GT & Gamma')
  (G':=GH ++ GT & Gamma' & Gamma);subst; try PPermut_LF_simpl.
clear H5 H6 IHHT.
assert (GH ++ Gamma'' :: GT & Gamma ~=~ G0 & Gamma'').
  transitivity G'; rew_app in *; auto; rewrite H0; auto.
assert (GH ++ GT & Gamma ~=~ G0).
  apply PPermut_LF_last_rev_simpl with (a:=Gamma'');
    rewrite <- H5; PPermut_LF_simpl.
apply PPermutationG_LF with (G := emptyEquiv_LF G'0); auto.
rewrite H1; rewrite <- H6; repeat rewrite emptyEquiv_LF_rewrite;
PPermut_LF_simpl.
rewrite H2.
rew_app; PPermut_LF_simpl; apply PPermut_LF_last_rev_simpl
  with (a:=(v,A0)::Gamma'0). rewrite <- H0; rewrite <- H; subst;
  PPermut_LF_simpl.

(* letdia *)
apply t_letdia_LF with (L := L \u \{v}) (A:=A);
[ apply ok_Bg_LF_permut_first_tail with (C:=Gamma) (x:=v) (A:=A0) |
  eapply IHHT |
  intros]; eauto;
unfold open_LF in *.
rewrite notin_union in H2; rewrite notin_singleton in H2; destruct H2.
rewrite <- subst_t_comm_LF. eapply H; eauto.
apply PPermutationG_LF with (G:=emptyEquiv_LF(((v0,A)::nil)::G)).
simpl. apply WeakeningG_LF. auto.
repeat apply ok_Bg_LF_nil; apply ok_Bg_LF_empty.
rewrite H3; auto.
auto. auto.

eapply t_letdia_LF with
  (L := L \u \{v}).
apply ok_Bg_LF_PPermut with (G:= (Gamma :: G0) & Gamma').
apply ok_Bg_LF_permut_no_last with (v:=v) (A:=A0).
rew_app. apply ok_Bg_LF_PPermut with (G:=Gamma :: G); auto.
rewrite H2; rew_app; auto.
eapply IHHT with (A0:=A0) ; eauto.
intros; unfold open_LF in *.
rewrite notin_union in H4; rewrite notin_singleton in H4; destruct H4;
rewrite <- subst_t_comm_LF; auto.
destruct H with (v:=v0) (M:=M0) (A:=A0) (v0:=v) (G':=((v0,A)::nil)::G); auto.
apply PPermutationG_LF with (G:=((v0,A)::nil)::G0 & Gamma').
eapply H8 with (G0:=G0 & ((v0, A)::nil)) (Gamma':=Gamma').
rewrite H0; PPermut_LF_simpl. eauto. PPermut_LF_simpl.
apply PPermutationG_LF with (G:=emptyEquiv_LF(((v0,A)::nil) ::G')).
simpl; apply WeakeningG_LF; auto.
repeat apply ok_Bg_LF_nil; apply ok_Bg_LF_empty.
rewrite H1; repeat rewrite emptyEquiv_LF_rewrite; simpl; PPermut_LF_simpl.
repeat rewrite emptyEquiv_LF_rewrite; simpl; auto.
rewrite <- H5. rewrite H2. auto.

(* letdia_get *)
eapply t_letdia_get_LF with (G:=G) (Gamma:=Gamma) (L := L \u \{v}) (A:=A);
auto.
apply ok_Bg_LF_permut_no_last_spec with (v:=v) (A:=A0);
apply ok_Bg_LF_PPermut with (G:= (Gamma) :: G & Gamma'); auto.
eapply IHHT with (Gamma'0:=Gamma0) (v:=v) (A0:=A0); auto.
apply PPermutationG_LF with (G:= emptyEquiv_LF(G0)); auto.
rewrite H0; auto.
intros; unfold open_LF in *.
rewrite notin_union in H3; rewrite notin_singleton in H3; destruct H3;
rewrite <- subst_t_comm_LF; auto.
destruct H with (v:=v0) (M:=M0)(A0:=A0)(v0:=v); auto.
eapply H5; eauto.
apply PPermutationG_LF with (G:= emptyEquiv_LF(nil::G0)); simpl; auto.
apply WeakeningG_LF; auto.
repeat apply ok_Bg_LF_nil; apply ok_Bg_LF_empty.
rewrite H0; auto.

destruct (permut_dec (var * ty) Gamma ((v,A0)::Gamma'0)).
  intros; destruct k; destruct k'; repeat decide equality.
  apply eq_var_dec.
(* = *)
assert (G ~=~ G1).
  apply PPermut_LF_last_rev with (Gamma:=Gamma)(Gamma':=(v,A0)::Gamma'0);
  auto.
  transitivity G0; auto.
apply t_letdia_get_LF with (G:=G1) (Gamma:=Gamma'0)
  (L:=L \u \{v}) (A:=A); eauto.
apply ok_Bg_LF_PPermut with (G:=Gamma'::G & Gamma'0); auto.
apply ok_Bg_LF_permut_no_last_spec with (v:=v)(A:=A0).
apply ok_Bg_LF_PPermut with (Gamma :: G & Gamma'); auto.
transitivity (Gamma :: Gamma' :: G).
PPermut_LF_simpl.
transitivity (Gamma' :: Gamma :: G).
PPermut_LF_simpl. constructor; auto. PPermut_LF_simpl.
rewrite H5. transitivity (Gamma' :: Gamma'0::G1).
constructor; auto; PPermut_LF_simpl.
transitivity (Gamma'0::Gamma'::G1); auto.
constructor; auto; PPermut_LF_simpl.
destruct IHHT with (M0:=M0) (v:=v) (A0:=A0); auto.
apply PPermutationG_LF with (G:=G & Gamma'); auto.
apply H6; auto.
apply PPermutationG_LF with (G:=emptyEquiv_LF G'); auto.
rewrite H5; rewrite H2; auto.
intros; unfold open_LF in *.
rewrite notin_union in H6; rewrite notin_singleton in H6; destruct H6;
rewrite <- subst_t_comm_LF; auto.
edestruct H with (v:=v0) (A0:=A0)
  (v0:=v) (M:=M0) as (Ha, Hb);
auto.
eapply Hb with (G0 := ((v0,A)::nil) ::G) (Gamma'0:=Gamma'0);
[ | auto |  | ]; try PPermut_LF_simpl.
rew_app; simpl. apply WeakeningG_LF.
apply PPermutationG_LF with (G:=emptyEquiv_LF G');
auto. rewrite H2; rewrite H5; auto.
repeat apply ok_Bg_LF_nil; apply ok_Bg_LF_empty.

(* <> *)
assert (G & (Gamma) ~=~ G1 & ((v, A0) :: Gamma'0)).
  (transitivity G0; auto).
symmetry in H5;
assert (exists Gamma0, exists GH, exists GT,
  Gamma0 *=* Gamma /\ G1 = GH & (Gamma0) ++ GT).
  (apply PPermut_LF_split_neq with (Gamma:=(v,A0) :: Gamma'0) (G':=G);
    auto).
  intro; elim n; symmetry; auto.
destruct H6 as (Gamma'', (GH, (GT, (H8, H9)))).
apply t_letdia_get_LF with (G:=GH++GT & (Gamma'0)) (Gamma:=Gamma) (A:=A)
  (L:=L \u \{v}); auto.
apply ok_Bg_LF_PPermut with (G:=Gamma' :: (G1 & Gamma'0)).
apply ok_Bg_LF_permut_no_last_spec with (v:=v)(A:=A0).
apply ok_Bg_LF_PPermut with (G:=Gamma :: G & Gamma'); auto.
transitivity ((G & Gamma) & Gamma'). auto.
rewrite <- H5. transitivity (G1 & Gamma' & ((v,A0)::Gamma'0)).
PPermut_LF_simpl. auto.
subst; PPermut_LF_simpl.
destruct IHHT with (M0:=M0) (A0:=A0) (v:=v); auto.
eapply H7 with (G0:=GH ++ GT & Gamma') (Gamma'0:=Gamma'0).
rew_app; PPermut_LF_simpl; subst.
apply PPermut_LF_last_rev with (Gamma:=Gamma) (Gamma':=Gamma'');
[ symmetry | ]; auto. rewrite <- H5.
PPermut_LF_simpl. eauto.
PPermut_LF_simpl.
apply PPermutationG_LF with (G:= emptyEquiv_LF(G')).
auto.
subst; rewrite H2; repeat rewrite emptyEquiv_LF_rewrite; simpl;
PPermut_LF_simpl.
intros; unfold open_LF in *.
rewrite notin_union in H6; rewrite notin_singleton in H6; destruct H6;
rewrite <- subst_t_comm_LF; auto.
destruct H with (v:=v0) (M:=M0) (A0:=A0) (v0:=v); auto.
eapply H11 with (G0:= G1 & ((v0,A)::nil)) (Gamma'0:=Gamma'0).
subst; rewrite <- H5; rew_app; PPermut_LF_simpl.
eauto.
subst; rew_app; PPermut_LF_simpl.
apply PPermutationG_LF with (G:=emptyEquiv_LF (((v0,A)::nil) :: G')).
simpl; apply WeakeningG_LF; auto.
repeat apply ok_Bg_LF_nil; apply ok_Bg_LF_empty.
subst; rewrite H2. apply Permut_emptyEquiv.
PPermut_LF_simpl.
rewrite H3; subst; PPermut_LF_simpl.
Qed.

Lemma subst_t_LF_preserv_types_inner:
forall G Gamma A B M N v
  (H_lc_t: lc_t_LF M)
  (HT: G |= (v, A) :: Gamma |- N ::: B)
  (HM: emptyEquiv_LF G |= nil |- M ::: A),
  G |= Gamma |- [M//fte v] N ::: B.
intros; eapply subst_t_LF_preserv_types with (Gamma := (v, A) :: Gamma); eauto.
Qed.

Lemma subst_t_LF_preserv_types_outer:
forall G0 G G' G'' Gamma Gamma' A B M N v
  (H_lc_t: lc_t_LF M)
  (G0G: G ~=~ (G0 & ((v, A) :: Gamma')))
  (G0G': G' ~=~ (G0 & Gamma))
  (G0G'': G'' ~=~ (G0 & Gamma'))
  (HM: emptyEquiv_LF G' |= nil |- M ::: A)
  (HT: G |= Gamma |- N ::: B),
  G'' |= Gamma |- [M // fte v] N ::: B.
intros; eapply subst_t_LF_preserv_types; eauto.
Qed.

Lemma merge_LF_preserv_types:
forall G Gamma M A
  (H: G |= Gamma |- M ::: A),
  (* outer *)
  (forall G0 G1 Gamma0 Delta0,
    G ~=~ Gamma0::Delta0::G0 ->
    G1 ~=~ (Gamma0++Delta0) :: G0 ->
    G1 |= Gamma |- M ::: A) /\
  (* new or old - by PermutationGamma_LF *)
  (forall G0 Delta0,
    G ~=~ Delta0 :: G0 ->
    G0 |= Gamma ++ Delta0 |- M ::: A).
intros; induction H; repeat split; intros.
(* hyp *)
constructor; auto.
eapply ok_Bg_LF_concat with (G0:=Gamma::G0) (c1:=Gamma0) (c2:=Delta0)
  (G1:=Gamma::G) (G2:=Gamma::G1);
eauto; [rewrite H0 | rewrite H1]; PPermut_LF_simpl.
constructor.
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G); eauto.
rewrite Mem_app_or_eq; left; auto.
(* lam *)
apply t_lam_LF with (L:=L).
eapply ok_Bg_LF_concat with (G0:=Gamma::G0) (G1:=Gamma::G); eauto;
try rewrite H2 || rewrite H1; auto; PPermut_LF_simpl.
intros; eapply H0; eauto.
apply t_lam_LF with (L:=L).
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G); eauto.
intros; eapply H0; eauto.
(* appl *)
apply t_appl_LF with (A:=A).
eapply ok_Bg_LF_concat with (G0:=Gamma::G0) (G1:=Gamma::G) (c1:=Gamma0)
  (c2:=Delta0); eauto;
try rewrite H2 || rewrite H1; eauto; PPermut_LF_simpl.
eapply IHtypes_LF1; eauto.
eapply IHtypes_LF2; eauto.
apply t_appl_LF with (A:=A).
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G); eauto.
eapply IHtypes_LF1; eauto.
eapply IHtypes_LF2; eauto.
(* box *)
constructor.
eapply ok_Bg_LF_concat with (G0:=G0 & Gamma) (G1:=G & Gamma)
  (c1:=Gamma0) (c2:=Delta0); eauto;
try rewrite H0 || rewrite H1; auto.
eapply IHtypes_LF with (G0:=G0 & Gamma) (Gamma0:=Gamma0) (Delta0:=Delta0);
eauto.
rewrite H0; PPermut_LF_simpl.
rewrite H1; PPermut_LF_simpl.
constructor.
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=G & Gamma)
  (c1:=Gamma) (c2:=Delta0); eauto; try PPermut_LF_simpl.
eapply IHtypes_LF with (G0:=G0) (Gamma0:=Gamma)
  (Delta0:=Delta0); eauto. rewrite H0; PPermut_LF_simpl. PPermut_LF_simpl.
(* unbox *)
constructor.
eapply ok_Bg_LF_concat with (G0:=Gamma::G0) (G1:=Gamma::G)
  (c1:=Gamma0)(c2:=Delta0); eauto;
try rewrite H0 || rewrite H1; PPermut_LF_simpl.
eapply IHtypes_LF; eauto.
constructor.
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G); eauto.
eapply IHtypes_LF; eauto.
(* Gamma *=* Gamma0 \/ Gamma *=* Gamma1 \/ neither *)
assert (G & Gamma ~=~ Gamma0 :: Delta0 :: G0).
  transitivity G'; auto.
assert ((Gamma *=* Gamma0 /\ G ~=~ Delta0::G0) \/
        (Gamma *=* Delta0 /\ G ~=~ Gamma0::G0) \/
        (exists c, exists hd, exists tl, Gamma *=* c /\ G0 = hd & c ++ tl)).
  assert ({Gamma *=* Gamma0} + {~ Gamma *=* Gamma0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  assert ({Gamma *=* Delta0} + {~ Gamma *=* Delta0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  destruct H4. left; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Gamma0); auto; rewrite H3; PPermut_LF_simpl.
  destruct H5.
  right; left; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Delta0); auto; rewrite H3; PPermut_LF_simpl.
  right; right.
  assert (G & Gamma ~=~ G0 & Delta0 & Gamma0) by (rewrite H3; PPermut_LF_simpl).
  symmetry in H4.
  apply PPermut_LF_split_neq in H4; auto.
  destruct H4 as (Gamma'', (hd, (tl, (H4, H5)))).
  assert (G0 & Delta0 ~=~ (hd ++ tl) & Gamma).
    rewrite H5; PPermut_LF_simpl.
  apply PPermut_LF_split_neq in H6; auto.
  destruct H6 as (Delta'', (hd', (tl', (H6, H7)))).
  exists Delta''; exists hd'; exists tl'; split; auto; symmetry; auto.
  intro nn; symmetry in nn; elim n0; auto.
  intro nn; symmetry in nn; elim n; auto.
destruct H4. destruct H4.
apply t_unbox_fetch_LF with (G:=G0) (Gamma:=Gamma0++Delta0).
eapply ok_Bg_LF_concat
 with (G0:=G0 & Gamma') (G1:=Gamma::G & Gamma'); eauto;
rewrite H5; auto.
apply PermutationGamma_LF with (Gamma:=Gamma++Delta0); auto.
eapply IHtypes_LF. rewrite H5; auto. rewrite H2; PPermut_LF_simpl.
destruct H4.
destruct H4.
apply t_unbox_fetch_LF with (G:=G0) (Gamma:=Delta0++Gamma0).
eapply ok_Bg_LF_concat
 with (G0:=G0 & Gamma') (G1:=Gamma::G & Gamma'); eauto;
rewrite H5; auto.
apply PermutationGamma_LF with (Gamma:=Gamma++Gamma0); auto.
eapply IHtypes_LF. rewrite H5; auto. rewrite H2; PPermut_LF_simpl.
destruct H4 as (c, (hd, (tl, (H4a, H4)))).
apply t_unbox_fetch_LF with (G:=(Gamma0++Delta0)::hd++tl) (Gamma:=c).
eapply ok_Bg_LF_concat with (G0:=G0 & Gamma') (G1:=Gamma::G & Gamma')
  (c1:=Gamma0) (c2:=Delta0); subst; auto.
transitivity (G & Gamma & Gamma'); auto; rewrite H3; subst; eauto;
PPermut_LF_simpl.
transitivity ((Gamma0++Delta0)::c::hd++tl & Gamma'); [PPermut_LF_simpl |].
rew_app; auto.
apply PermutationGamma_LF with (Gamma:=Gamma); auto.
assert (G ~=~ Gamma0::Delta0::hd ++ tl).
  subst; apply PPermut_LF_last_rev with (Gamma:=Gamma) (Gamma':=c); auto;
  rewrite H3; PPermut_LF_simpl.
eapply IHtypes_LF with (Gamma0:=Gamma0) (Delta0:=Delta0) (G0:=hd ++tl & Gamma');
eauto.
rewrite H5. rew_app; auto. rew_app; auto. rewrite H2; subst; PPermut_LF_simpl.
assert (G & Gamma ~=~ Delta0 :: G0).
  transitivity G'; auto.
assert ((Gamma *=* Delta0 /\ G ~=~ G0) \/
        (exists c, exists hd, exists tl, c *=* Gamma /\ G0 = hd & c ++ tl)).
  assert ({Gamma *=* Delta0} + {~ Gamma *=* Delta0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  destruct H3. left; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Delta0); auto; rewrite H2; PPermut_LF_simpl.
  right.
  assert (G & Gamma ~=~ G0 & Delta0) by (rewrite H2; PPermut_LF_simpl).
  symmetry in H3.
  apply PPermut_LF_split_neq in H3; auto.
  intro nn; symmetry in nn; elim n; auto.
destruct H3.
destruct H3.
constructor.
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G & Gamma'); eauto;
rewrite H4; PPermut_LF_simpl.
apply PermutationGamma_LF with (Gamma:=Gamma++Gamma').
eapply IHtypes_LF. rewrite H4; PPermut_LF_simpl.
permut_simpl; auto.
destruct H3 as (c, (hd, (tl, (H3a, H3)))); subst.
apply t_unbox_fetch_LF with (G:=hd++tl) (Gamma:=Gamma).
eapply ok_Bg_LF_concat with (G0:=Gamma::(hd++tl)) (G1:=Gamma::G & Gamma')
  (c1:=Gamma')(c2:=Delta0);
eauto.
transitivity (G & Gamma & Gamma'); auto; rewrite H2; PPermut_LF_simpl.
PPermut_LF_simpl.
assert (G ~=~ Delta0::hd ++ tl).
  apply PPermut_LF_last_rev with (Gamma:=Gamma) (Gamma':=c). symmetry; auto.
  rewrite H2; PPermut_LF_simpl.
eapply IHtypes_LF with (Gamma0:=Gamma') (Delta0 :=Delta0) (G0:= hd ++ tl).
rewrite H3; PPermut_LF_simpl. PPermut_LF_simpl. PPermut_LF_simpl.
(* here *)
constructor.
eapply ok_Bg_LF_concat with (G0:=Gamma::G0) (G1:=Gamma::G)
  (c1:=Gamma0)(c2:=Delta0); eauto;
try rewrite H0 || rewrite H1; PPermut_LF_simpl.
eapply IHtypes_LF; eauto.
constructor.
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G); eauto.
eapply IHtypes_LF; eauto.
(* Gamma *=* Gamma0 \/ Gamma *=* Gamma1 \/ neither *)
assert (G & Gamma ~=~ Gamma0 :: Delta0 :: G0).
  transitivity G'; auto.
assert ((Gamma *=* Gamma0 /\ G ~=~ Delta0::G0) \/
        (Gamma *=* Delta0 /\ G ~=~ Gamma0::G0) \/
        (exists c, exists hd, exists tl, Gamma *=* c /\ G0 = hd & c ++ tl)).
  assert ({Gamma *=* Gamma0} + {~ Gamma *=* Gamma0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  assert ({Gamma *=* Delta0} + {~ Gamma *=* Delta0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  destruct H4. left; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Gamma0); auto; rewrite H3; PPermut_LF_simpl.
  destruct H5.
  right; left; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Delta0); auto; rewrite H3; PPermut_LF_simpl.
  right; right.
  assert (G & Gamma ~=~ G0 & Delta0 & Gamma0) by (rewrite H3; PPermut_LF_simpl).
  symmetry in H4.
  apply PPermut_LF_split_neq in H4; auto.
  destruct H4 as (Gamma'', (hd, (tl, (H4, H5)))).
  assert (G0 & Delta0 ~=~ (hd ++ tl) & Gamma).
    rewrite H5; PPermut_LF_simpl.
  apply PPermut_LF_split_neq in H6; auto.
  destruct H6 as (Delta'', (hd', (tl', (H6, H7)))).
  exists Delta''; exists hd'; exists tl'; split; auto; symmetry; auto.
  intro nn; symmetry in nn; elim n0; auto.
  intro nn; symmetry in nn; elim n; auto.
destruct H4. destruct H4.
apply t_get_here_LF with (G:=G0) (Gamma:=Gamma0++Delta0).
eapply ok_Bg_LF_concat
 with (G0:=G0 & Gamma') (G1:=Gamma::G & Gamma'); eauto;
rewrite H5; auto.
apply PermutationGamma_LF with (Gamma:=Gamma++Delta0); auto.
eapply IHtypes_LF. rewrite H5; auto. rewrite H2; PPermut_LF_simpl.
destruct H4.
destruct H4.
apply t_get_here_LF with (G:=G0) (Gamma:=Delta0++Gamma0).
eapply ok_Bg_LF_concat with (G0:=G0 & Gamma') (G1:=Gamma::G & Gamma')
  (c1:=Gamma0) (c2:=Delta0); subst; auto.
transitivity (G & Gamma & Gamma'); auto; rewrite H3; subst; eauto;
PPermut_LF_simpl.
apply PermutationGamma_LF with (Gamma:=Gamma++Gamma0); auto.
eapply IHtypes_LF. rewrite H5; auto. rewrite H2; PPermut_LF_simpl.
destruct H4 as (c, (hd, (tl, (H4a, H4)))).
apply t_get_here_LF with (G:=(Gamma0++Delta0)::hd++tl) (Gamma:=c).
eapply ok_Bg_LF_concat with (G0:=G0 & Gamma') (G1:=Gamma::G & Gamma')
  (c1:=Gamma0) (c2:=Delta0); subst; auto.
transitivity (G & Gamma & Gamma'); auto; rewrite H3; subst; eauto;
PPermut_LF_simpl.
transitivity ((Gamma0++Delta0)::c::hd++tl & Gamma'); [PPermut_LF_simpl |].
rew_app; auto.
apply PermutationGamma_LF with (Gamma:=Gamma); auto.
assert (G ~=~ Gamma0::Delta0::hd ++ tl).
  subst; apply PPermut_LF_last_rev with (Gamma:=Gamma) (Gamma':=c); auto;
  rewrite H3; PPermut_LF_simpl.
eapply IHtypes_LF with (Gamma0:=Gamma0) (Delta0:=Delta0) (G0:=hd ++tl & Gamma');
eauto.
rewrite H5. rew_app; auto. rew_app; auto. rewrite H2; subst; PPermut_LF_simpl.
assert (G & Gamma ~=~ Delta0 :: G0).
  transitivity G'; auto.
assert ((Gamma *=* Delta0 /\ G ~=~ G0) \/
        (exists c, exists hd, exists tl, c *=* Gamma /\ G0 = hd & c ++ tl)).
  assert ({Gamma *=* Delta0} + {~ Gamma *=* Delta0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  destruct H3. left; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Delta0); auto; rewrite H2; PPermut_LF_simpl.
  right.
  assert (G & Gamma ~=~ G0 & Delta0) by (rewrite H2; PPermut_LF_simpl).
  symmetry in H3.
  apply PPermut_LF_split_neq in H3; auto.
  intro nn; symmetry in nn; elim n; auto.
destruct H3.
destruct H3.
constructor.
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G & Gamma'); eauto;
rewrite H4; PPermut_LF_simpl.
apply PermutationGamma_LF with (Gamma:=Gamma++Gamma').
eapply IHtypes_LF. rewrite H4; PPermut_LF_simpl.
permut_simpl; auto.
destruct H3 as (c, (hd, (tl, (H3a, H3)))); subst.
apply t_get_here_LF with (G:=hd++tl) (Gamma:=Gamma).
eapply ok_Bg_LF_concat with (G0:=Gamma::(hd++tl)) (G1:=Gamma::G & Gamma')
  (c1:=Gamma')(c2:=Delta0);
eauto.
transitivity (G & Gamma & Gamma'); auto; rewrite H2; PPermut_LF_simpl.
PPermut_LF_simpl.
assert (G ~=~ Delta0::hd ++ tl).
  apply PPermut_LF_last_rev with (Gamma:=Gamma) (Gamma':=c). symmetry; auto.
  rewrite H2; PPermut_LF_simpl.
eapply IHtypes_LF with (Gamma0:=Gamma') (Delta0 :=Delta0) (G0:= hd ++ tl).
rewrite H3; PPermut_LF_simpl. PPermut_LF_simpl. PPermut_LF_simpl.
(* letdia *)
apply t_letdia_LF with (L:=L) (A:=A).
eapply ok_Bg_LF_concat with (G0:=Gamma::G0) (G1:=Gamma::G) (c1:=Gamma0)
  (c2:=Delta0);
eauto; rewrite H1 || rewrite H2; auto; PPermut_LF_simpl.
  eapply IHtypes_LF; eauto. intros.
  apply PPermutationG_LF with  (G:=((v, A) :: nil) :: G1).
  apply PPermutationG_LF with (G:= ((v,A)::nil)::(Gamma0 ++ Delta0) :: G0).
  eapply H0 with (G':=((v,A)::nil)::G) (G0:= ((v,A)::nil)::G0)
    (Delta0:=Delta0)(Gamma0:=Gamma0); eauto.
  PPermut_LF_simpl. PPermut_LF_simpl; auto. auto.
apply t_letdia_LF with (L:=L) (A:=A).
eapply ok_Bg_LF_concat with (G0:=G0) (G1:=Gamma::G) (c1:=Gamma)
  (c2:=Delta0);
eauto.
  eapply IHtypes_LF; eauto. intros.
  apply PPermutationG_LF with (G:=((v, A) :: nil) :: G0).
  eapply H0 with (G':=((v,A)::nil)::G); eauto.
  rewrite H1; PPermut_LF_simpl. auto.
assert (G & Gamma ~=~ Gamma0 :: Delta0 :: G1).
  transitivity G0; auto.
assert ((Gamma *=* Gamma0 /\ G ~=~ Delta0::G1) \/
        (Gamma *=* Delta0 /\ G ~=~ Gamma0::G1) \/
        (exists c, exists hd, exists tl, Gamma *=* c /\ G1 = hd & c ++ tl)).
  assert ({Gamma *=* Gamma0} + {~ Gamma *=* Gamma0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  assert ({Gamma *=* Delta0} + {~ Gamma *=* Delta0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  destruct H5. left; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Gamma0); auto; rewrite H4; PPermut_LF_simpl.
  destruct H6.
  right; left; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Delta0); auto; rewrite H4; PPermut_LF_simpl.
  right; right.
  assert (G & Gamma ~=~ G1 & Delta0 & Gamma0) by (rewrite H4; PPermut_LF_simpl).
  symmetry in H5.
  apply PPermut_LF_split_neq in H5; auto.
  destruct H5 as (Gamma'', (hd, (tl, (H5, H6)))).
  assert (G1 & Delta0 ~=~ (hd ++ tl) & Gamma).
    rewrite H6; PPermut_LF_simpl.
  apply PPermut_LF_split_neq in H7; auto.
  destruct H7 as (Delta'', (hd', (tl', (H7, H8)))).
  exists Delta''; exists hd'; exists tl'; split; auto; symmetry; auto.
  intro nn; symmetry in nn; elim n0; auto.
  intro nn; symmetry in nn; elim n; auto.
destruct H5. destruct H5.
apply t_letdia_get_LF with (G:=G1) (Gamma:=Gamma++Delta0) (L:=L) (A:=A).
eapply ok_Bg_LF_concat with (G0:=G1 & Gamma') (G1:=Gamma::G & Gamma'); eauto;
rewrite H6; auto.
eapply IHtypes_LF.
rewrite H6; PPermut_LF_simpl.
intros. eapply H0 with (G0:=((v,A)::nil)::G1) (Gamma0:=Gamma0)(Delta0:=Delta0);
eauto. rewrite H6; PPermut_LF_simpl. PPermut_LF_simpl.
rewrite H3; PPermut_LF_simpl.
destruct H5. destruct H5.
apply t_letdia_get_LF with (G:=G1) (Gamma:=Gamma++Gamma0) (A:=A) (L:=L).
eapply ok_Bg_LF_concat with (G0:=G1 & Gamma') (G1:=Gamma::G & Gamma'); eauto;
rewrite H6; auto.
eapply IHtypes_LF. rewrite H6; PPermut_LF_simpl.
intros.
eapply H0 with (G0:=((v,A)::nil)::G1) (Gamma0:=Gamma0)(Delta0:=Delta0);
eauto. rewrite H6; PPermut_LF_simpl. PPermut_LF_simpl; constructor. rewrite H5.
auto. auto. rewrite H3; PPermut_LF_simpl. constructor; auto; rewrite H5; auto.
destruct H5 as (c, (hd, (tl, (H5a, H5)))).
apply t_letdia_get_LF with
  (G:=(Gamma0++Delta0)::hd++tl)(Gamma:=Gamma) (L:=L)(A:=A).
eapply ok_Bg_LF_concat with (G0:=Gamma::(hd++tl)&Gamma') (G1:=Gamma::G & Gamma')
  (c1:=Gamma0)(c2:=Delta0);
eauto.
transitivity (G & Gamma & Gamma'); auto; rewrite H4; subst; PPermut_LF_simpl.
PPermut_LF_simpl.
rew_app.
eapply IHtypes_LF with (G0:=hd++tl & Gamma') (Gamma0:=Gamma0)(Delta0:=Delta0);
eauto. PPermut_LF_simpl; rew_app.
subst.
apply PPermut_LF_last_rev with (Gamma:=Gamma) (Gamma':=c); auto; rewrite H4;
PPermut_LF_simpl.
intros. rew_app.
eapply H0 with (G0:=((v,A)::nil)::G1) (Gamma0:=Gamma0) (Delta0:=Delta0);
eauto.
rewrite H4; PPermut_LF_simpl.
subst; PPermut_LF_simpl. rewrite H3; subst; PPermut_LF_simpl.
assert (G & Gamma ~=~ Delta0 :: G1).
  transitivity G0; auto.
assert ((Gamma *=* Delta0 /\ G ~=~ G1) \/
        (exists c, exists hd, exists tl, Gamma *=* c /\ G1 = hd & c ++ tl)).
  assert ({Gamma *=* Delta0} + {~ Gamma *=* Delta0}).
  apply permut_dec. intros. destruct k; destruct k'; decide equality.
  apply eq_ty_dec. apply eq_var_dec.
  destruct H4. left; split; auto. apply PPermut_LF_last_rev with (Gamma:=Gamma)
  (Gamma':=Delta0); auto; rewrite H3; PPermut_LF_simpl.
  right.
  assert (G & Gamma ~=~ G1 & Delta0) by (rewrite H3; PPermut_LF_simpl).
  symmetry in H4.
  apply PPermut_LF_split_neq in H4; auto.
  destruct H4 as (Gamma'', (hd, (tl, (H5, H6)))).
  exists Gamma''; exists hd; exists tl; split.
  symmetry; auto. auto.
  intro nn; symmetry in nn; elim n; auto.
destruct H4.
destruct H4.
apply t_letdia_LF with (A:=A)(L:=L).
eapply ok_Bg_LF_concat with (G0:=G1) (G1:=Gamma::G & Gamma')
  (c1:=Gamma')(c2:=Delta0);
eauto; rewrite H5; auto; PPermut_LF_simpl.
apply PermutationGamma_LF with (Gamma:=Gamma++Gamma').
eapply IHtypes_LF; eauto.
rewrite H5; PPermut_LF_simpl. rewrite H4; auto.
intros.
eapply H0; eauto.
rewrite <- H7; rewrite H5; PPermut_LF_simpl.
destruct H4 as (c, (hd, (tl, (H4a, H4)))).
apply t_letdia_get_LF with
  (G:=hd++tl)(Gamma:=Gamma) (L:=L)(A:=A).
eapply ok_Bg_LF_concat with (G0:=Gamma::(hd++tl)) (G1:=Gamma::G & Gamma')
  (c1:=Gamma')(c2:=Delta0);
eauto.
transitivity (G & Gamma & Gamma'); auto; rewrite H3; subst; PPermut_LF_simpl.
PPermut_LF_simpl.
subst. rew_app.
eapply IHtypes_LF with (G0:=hd++tl) (Gamma0:=Gamma')(Delta0:=Delta0);
eauto. PPermut_LF_simpl; apply PPermut_LF_last_rev with (Gamma:=Gamma)
(Gamma':=c);
auto; rewrite H3; PPermut_LF_simpl. PPermut_LF_simpl.
intros; subst; rew_app.
eapply H0; eauto. rewrite H3; PPermut_LF_simpl. subst; PPermut_LF_simpl.
Qed.

Lemma merge_LF_preserv_types_outer:
forall G G0 G1 Gamma Gamma0 Delta0 M A,
  G |= Gamma |- M ::: A ->
  G ~=~ Gamma0 :: Delta0 :: G0 ->
  G1 ~=~ (Gamma0 ++ Delta0) :: G0 ->
  G1 |= Gamma |- M ::: A.
intros; eapply merge_LF_preserv_types; eauto.
Qed.

Lemma merge_LF_preserv_types_new:
forall G G0 Gamma Delta M A,
  G |= Gamma |- M ::: A ->
  G ~=~ Delta::G0 ->
  G0 |= Gamma++Delta |- M ::: A.
intros; eapply merge_LF_preserv_types with (G:=G) (Gamma:=Gamma); eauto.
Qed.

Lemma merge_LF_preserv_types_old:
forall G G0 Gamma Delta M A,
  G |= Delta |- M ::: A ->
  G ~=~ Gamma::G0 ->
  G0 |= Gamma++Delta |- M ::: A.
intros;
apply PermutationGamma_LF with (Gamma:=Delta++Gamma).
eapply merge_LF_preserv_types; eauto.
auto.
Qed.

Lemma Progress_LF:
forall G M A
  (H_lc_t: lc_t_LF M)
  (HT: emptyEquiv_LF G |= nil |- M ::: A),
  value_LF M \/ exists N, M |-> N.
intros;
remember (@nil (var * ty)) as Ctx;
generalize dependent Ctx;
generalize dependent A;
generalize dependent G;
induction M; intros; eauto using value_LF;
inversion HeqCtx; subst.
(* hyp *)
inversion HT; subst.
rewrite Mem_nil_eq in H3;
contradiction.
(* appl *)
right; inversion HT; subst;
inversion H_lc_t; subst;
edestruct IHM1 with (A := A0 ---> A); eauto;
[inversion H0; subst; inversion H4; subst | inversion H0];
eexists; constructor; eauto;
inversion H3; subst; auto.
(* unbox *)
right; inversion HT; subst;
inversion H_lc_t; subst.
edestruct IHM with (A := [*]A); eauto;
[ inversion H0; subst; inversion H3; subst; inversion H3 |
  destruct H0];
eexists; constructor; eauto;
inversion H1; inversion H2; subst; auto.
assert (Gamma = nil) by
  ( apply emptyEquiv_LF_permut_empty with
    (G:= G0 & Gamma) (G':=G); auto;
    apply Mem_last); subst.
destruct IHM with (A := [*]A)
                  (Ctx := (@nil (var * ty)))
                  (G := G0 & nil);
eauto.

assert (emptyEquiv_LF (G0 & nil) = G0 & nil).
  eapply emptyEquiv_LF_PPermut_eq; eauto.
rewrite H0; auto.
inversion H0; subst; inversion H1; subst.
eexists; constructor; eauto. inversion H3; auto; subst.
destruct H0; eexists; econstructor; eauto.
(* here *)
inversion HT; subst;
inversion H_lc_t; subst.
edestruct IHM; eauto;
[left; econstructor | right; destruct H0; eexists];
eauto using step_LF.
assert (Gamma = nil) by
  ( apply emptyEquiv_LF_permut_empty with
    (G:= G0 & Gamma) (G':=G); auto;
    apply Mem_last); subst;
destruct IHM with (A := A0)
                  (Ctx := (@nil (var*ty)))
                  (G := G0 & nil);
eauto.
assert (emptyEquiv_LF (G0 & nil) = G0 & nil) by
  (eapply emptyEquiv_LF_PPermut_eq; eauto).
rewrite H0; auto.
left; inversion H0; subst; inversion H4; subst;
econstructor; eauto using step_LF.
right; destruct H0; eexists;
econstructor; eauto using step_LF.
(* letdia *)
right; inversion HT; subst;
inversion H_lc_t; subst.
edestruct IHM1 with (A := <*>A0); eauto;
[ inversion H0; subst; inversion HT1; subst |
  destruct H0];
eexists; constructor; eauto.
inversion H5; subst; auto.
inversion H5; subst; auto.
assert (Gamma = nil) by
  ( apply emptyEquiv_LF_permut_empty with (G:= G0 & Gamma) (G':=G);
    auto; apply Mem_last); subst;
edestruct IHM1 with (G := G0 & nil)
                    (Ctx := (@nil (var*ty)))
                    (A := <*>A0); eauto;
assert ( emptyEquiv_LF (G0 & nil) = G0 & nil) by
  (eapply emptyEquiv_LF_PPermut_eq; eauto).
rewrite H0; auto.
inversion H0; subst; inversion HT1; subst;
eexists; constructor; eauto;
inversion H5; subst; auto.
destruct H0;
eexists; econstructor; eauto.
Qed.

Lemma Preservation_LF:
forall G M N A
  (HT: emptyEquiv_LF G |= nil |- M ::: A)
  (HS: M |-> N),
  emptyEquiv_LF G |= nil |- N ::: A.
intros; generalize dependent N.
remember (emptyEquiv_LF G) as G';
remember (@nil (var*ty)) as Gamma.
generalize dependent G.
induction HT; intros;
inversion HS; subst;
try (econstructor; eauto).

(* appl_lam *)
inversion HT1; subst;
unfold open_LF in *;
assert (exists v, v \notin L \u used_vars_te_LF M0) as HF by apply Fresh;
destruct HF as (v_fresh);
rewrite subst_t_neutral_free_LF with (v:=v_fresh);
[ eapply subst_t_LF_preserv_types_inner; eauto |
  rewrite notin_union in H; destruct H]; auto;
rewrite <- double_emptyEquiv_LF; auto.

(* unbox_box *)
inversion HT; subst;
replace (@nil (var * ty)) with (nil ++ (@nil (prod var ty)))
  by (rew_app; auto);
apply merge_LF_preserv_types_old with (G:=emptyEquiv_LF G0 & nil);
rew_app; auto.
transitivity (emptyEquiv_LF (G0&nil)).
  rewrite emptyEquiv_LF_rewrite; auto.
  transitivity (emptyEquiv_LF (nil :: G0)); auto.

apply PPermut_emptyEquiv_LF; PPermut_LF_simpl.

inversion HT; subst;
replace (@nil (var * ty)) with (nil ++ (@nil (prod var ty)))
  by (rew_app; auto);
apply merge_LF_preserv_types_old with (G:=G & nil & Gamma);
auto. rewrite <- H; auto.
apply ok_Bg_LF_nil; apply ok_Bg_LF_empty.
assert (Gamma = nil).
  apply emptyEquiv_LF_PPermut in H; auto.
subst. replace (emptyEquiv_LF G0) with (G & nil).
apply IHHT with (G0:=G0); auto.
apply emptyEquiv_LF_PPermut_equal; auto.
apply emptyEquiv_LF_PPermut_equal; auto.

(* here *)
apply ok_Bg_LF_nil; apply ok_Bg_LF_empty.
assert (Gamma = nil).
  apply emptyEquiv_LF_PPermut in H; auto.
subst. replace (emptyEquiv_LF G0) with (G & nil).
apply IHHT with (G0:=G0); auto.
apply emptyEquiv_LF_PPermut_equal; auto.
apply emptyEquiv_LF_PPermut_equal; auto.
inversion HT; subst;
unfold open_LF in *;
assert (exists v, v \notin L \u used_vars_te_LF N) as HF by apply Fresh;
destruct HF as (v_fresh);
rewrite subst_t_neutral_free_LF with (v:=v_fresh);
replace (@nil (var * ty)) with (nil ++ (@nil (prod var ty)))
  by (rew_app; auto).

apply merge_LF_preserv_types_old with (G:=emptyEquiv_LF G0 & nil);
rew_app; auto.
apply subst_t_LF_preserv_types_outer with
  (A:=A) (G:=((v_fresh, A) :: nil) :: emptyEquiv_LF G0) (G0:=emptyEquiv_LF G0)
  (Gamma':=nil) (G':=emptyEquiv_LF G0 & nil); eauto.
PPermut_LF_simpl.
assert (emptyEquiv_LF G0 & nil = emptyEquiv_LF (G0 & nil)).
  rewrite emptyEquiv_LF_rewrite; simpl; auto.
rewrite H1; rewrite <- double_emptyEquiv_LF; rewrite <- H1.
assert (emptyEquiv_LF G0 & nil ~=~ nil::emptyEquiv_LF G0).
  PPermut_LF_simpl.
rewrite H2.
apply WeakeningG_LF; auto.
symmetry;
remember (emptyEquiv_LF G0) as G'.
apply PPermut_LF_first_last.
eauto.
apply merge_LF_preserv_types_old with (G:=emptyEquiv_LF G0 & nil).
apply subst_t_LF_preserv_types_outer with
  (A:=A) (G:=((v_fresh, A) :: nil) :: emptyEquiv_LF G0) (G0:=emptyEquiv_LF G0)
  (Gamma':=nil) (G':=emptyEquiv_LF G0 & nil); eauto.
PPermut_LF_simpl.
replace (emptyEquiv_LF G0 & nil) with (emptyEquiv_LF (G0 & nil)).
rewrite <- double_emptyEquiv_LF.
assert (Gamma = nil).
  apply emptyEquiv_LF_PPermut in H8; auto.
subst.
rewrite emptyEquiv_LF_rewrite; rewrite <- H8; simpl.
apply PPermutationG_LF with (G:=nil :: G & nil); auto;
apply WeakeningG_LF; auto.
rewrite emptyEquiv_LF_rewrite;simpl; auto.
symmetry; apply PPermut_LF_first_last.
eauto.
inversion HT; subst;
unfold open_LF in *;
assert (exists v, v \notin L \u used_vars_te_LF N) as HF by apply Fresh;
destruct HF as (v_fresh);
rewrite subst_t_neutral_free_LF with (v:=v_fresh);
replace (@nil (var * ty)) with (nil ++ (@nil (prod var ty)))
  by (rew_app; auto).
apply merge_LF_preserv_types_old with (G:=emptyEquiv_LF G1 & nil);
rew_app; auto.
apply subst_t_LF_preserv_types_outer with
  (A:=A) (G:=((v_fresh, A) :: nil) :: emptyEquiv_LF G1) (G0:=emptyEquiv_LF G1)
  (Gamma':=nil) (G':=emptyEquiv_LF G1 & nil); eauto.
 PPermut_LF_simpl.
assert (emptyEquiv_LF G1 & nil = emptyEquiv_LF (G1 & nil)).
  rewrite emptyEquiv_LF_rewrite; simpl; auto.
rewrite H2; rewrite <- double_emptyEquiv_LF; rewrite <- H2.
assert (emptyEquiv_LF G1 & nil ~=~ nil::emptyEquiv_LF G1).
  PPermut_LF_simpl.
rewrite H3.
apply WeakeningG_LF; auto.
rewrite <- H0;
assert (Gamma = nil).
  apply emptyEquiv_LF_PPermut in H0; auto.
subst Gamma; auto.
repeat apply ok_Bg_LF_nil; apply ok_Bg_LF_empty.
rewrite <- H0;
apply HT2; eauto.
symmetry; apply PPermut_LF_first_last.
eauto.

apply merge_LF_preserv_types_old with (G:=emptyEquiv_LF G1 & nil);
rew_app; auto.
apply subst_t_LF_preserv_types_outer with
  (A:=A) (G:=((v_fresh, A) :: nil) :: emptyEquiv_LF G1) (G0:=emptyEquiv_LF G1)
  (Gamma':=nil) (G':=emptyEquiv_LF G1 & nil); eauto.
PPermut_LF_simpl.
assert (emptyEquiv_LF G1 & nil = emptyEquiv_LF (G1 & nil)).
  rewrite emptyEquiv_LF_rewrite; simpl; auto.
rewrite H2; rewrite <- double_emptyEquiv_LF; rewrite <- H2.
assert (emptyEquiv_LF G1 & nil ~=~ nil::emptyEquiv_LF G1).
  symmetry; apply PPermut_LF_first_last.
rewrite H3;
apply WeakeningG_LF; rewrite <- H0; auto.
assert (Gamma = nil).
  apply emptyEquiv_LF_PPermut in H0; auto.
subst.
assert (Gamma0 = nil).
  rewrite H0 in H9; apply emptyEquiv_LF_PPermut in H9; auto.
subst.
assert (G0 ~=~ G).
  apply PPermut_LF_last_rev_simpl with (a:=nil); auto.
rewrite <- H9; auto.
repeat apply ok_Bg_LF_nil; rewrite H0; apply ok_Bg_LF_empty.
rewrite <- H0;
apply HT2; eauto.
symmetry; apply PPermut_LF_first_last.
eauto.

apply ok_Bg_LF_nil; apply ok_Bg_LF_empty.
assert (Gamma = nil).
  apply emptyEquiv_LF_PPermut in H0; auto.
subst.
rewrite <- H0. apply IHHT with (G0:=G1); auto.
apply emptyEquiv_LF_PPermut_equal; auto.

intros. unfold open_LF in *.
assert (Gamma = nil).
  apply emptyEquiv_LF_PPermut in H0; auto.
subst.
rewrite <- H2. rewrite <- H0.
apply HT2; eauto.
Qed.

Lemma lc_t_step_LF:
forall M N,
  lc_t_LF M ->
  M |-> N ->
  lc_t_LF N.
induction M; intros; inversion H0; inversion H; subst; try constructor; eauto;
unfold open_LF in *.
apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
eapply IHM; eauto.
eapply IHM; eauto.
apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
Qed.

Notation " M |->* N " := (steps_LF M N) (at level 70).

Lemma lc_t_steps_LF:
forall M N, lc_t_LF M -> M |->* N -> lc_t_LF N.
intros; induction H0. auto.
apply IHclos_refl_trans_1n.
apply lc_t_step_LF in H0; auto.
Qed.

Lemma value_no_step_LF:
forall M,
  value_LF M ->
  forall N , ~ M |-> N.
induction M; intros; intro;
try inversion H; inversion H0; subst; try inversion H2;
eapply IHM; eauto.
Qed.

Lemma eq_te_LF_dec:
forall (M1: te_LF) (M2: te_LF),
  {M1 = M2} + {M1 <> M2}.
decide equality.
apply eq_vte_dec.
apply eq_ty_dec.
apply eq_ty_dec.
Qed.

Instance Steps_Reflexive: Reflexive steps_LF := {
}.
unfold Reflexive. intros; constructor.
Qed.

Instance Steps_Transitive: Transitive steps_LF := {
}.
unfold Transitive. intros.
induction H; auto. constructor 2 with (y:=y); auto.
apply IHclos_refl_trans_1n. auto.
Qed.
