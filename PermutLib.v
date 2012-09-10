Require Import Setoid.
Require Export LibListSorted.
Require Export LibList.
Require Export LibRelation.


Notation " Ctx *=* Ctx'" := (permut Ctx Ctx') (at level 70) : permut_scope.

Lemma Permut_refl:
forall (A: Type),
  Reflexive (@permut A).
unfold Reflexive; intros; apply permut_refl.
Qed.

Lemma Permut_sym:
forall (A: Type),
  Symmetric (@permut A).
unfold Symmetric; intros; apply permut_sym; auto.
Qed.

Lemma Permut_trans:
forall (A: Type),
  Transitive (@permut A).
unfold Transitive; intros; eapply permut_trans; eauto.
Qed.

Instance Permut_Equivalence A : Equivalence (@permut A) | 10 := {
  Equivalence_Reflexive := @Permut_refl A ;
  Equivalence_Symmetric := @Permut_sym A ;
  Equivalence_Transitive := @Permut_trans A }.
Hint Resolve Permut_refl Permut_sym.

Open Scope permut_scope.

Add Parametric Morphism A (a:A) : (cons a)
  with signature @permut A ==> @permut A
  as Permut_cons.
auto.
Qed.

Add Parametric Morphism A : (@append A)
  with signature @permut A ==> @permut A ==> @permut A
  as Permut_append.
auto.
Qed.

Hint Resolve Permut_cons Permut_append.

Lemma permut_nil_eq:
forall A L, nil *=* L -> L = (@nil A).
unfold permut; intros;
remember (@nil A) as L';
induction H; [ auto | subst];
inversion H;
apply app_eq_nil_inv in H2; destruct H2;
apply app_eq_nil_inv in H3; destruct H3;
apply app_eq_nil_inv in H4; destruct H4;
subst; rew_app in *;
apply IHrtclosure; auto.
Qed.

Lemma permut_cons_eq:
forall A L (a: A), (a::nil) *=* L -> L = a :: nil.
unfold permut; intros;
remember (a::nil) as L';
generalize dependent a;
induction H; intros; [auto | subst];
inversion H;
destruct l1; destruct l2; destruct l3; destruct l4;
rew_app in *;
inversion H2; subst;
try eapply IHrtclosure; eauto;
symmetry in H5; apply nil_eq_app_inv in H5; destruct H5; inversion H3.
Qed.

Lemma Mem_split:
forall A l (a: A),
  Mem a l ->
  exists hd, exists tl, l = hd & a ++ tl.
induction l; intros;
[rewrite Mem_nil_eq in H; contradiction |
 rewrite Mem_cons_eq in H; destruct H]; subst;
[exists nil; exists l; rew_app; auto | ];
apply IHl in H; destruct H as (hd); destruct H as (tl); subst;
exists (a::hd); exists tl; rew_app; auto.
Qed.

Lemma Mem_permut:
forall A (l l' : list A) (x : A),
  l *=* l' ->
  Mem x l ->
  Mem x l'.
intros; induction H; auto;
apply IHrtclosure;
inversion H; subst;
repeat rewrite Mem_app_or_eq in H0;
repeat rewrite Mem_app_or_eq;
repeat (destruct H0; auto).
Qed.

Lemma permut_split_head:
forall A l1 l2 (a: A), (a::l1) *=* l2 ->
  exists hd, exists tl, l2 = hd & a ++ tl.
intros; apply Mem_split; eapply Mem_permut; eauto;
apply Mem_here.
Qed.

Lemma permut_app_inv:
forall A l1 l2 l3 l4 (a:A),
  l1 & a ++ l2 *=* l3 & a ++ l4 ->
  l1 ++ l2 *=* l3 ++ l4.
Admitted. (* !!! Bug: #39 *)

Lemma permut_cons_inv:
forall A l1 l2 (a:A),
  a::l1 *=* a::l2 ->
  l1 *=* l2.
intros; apply (permut_app_inv A nil l1 nil l2 a); rew_app; auto.
Qed.

Lemma permut_neq_split:
forall A l1 l2 (a:A) b,
  a <> b ->
  Mem a l1 ->
  l1 *=* b :: l2 ->
  exists gh, exists gt, l2 = gh & a ++ gt.
intros; apply Mem_split;
assert (Mem a (b::l2)) by (eapply Mem_permut; eauto);
apply Mem_inv in H2; destruct H2; [ contradiction | destruct H2]; auto.
Qed.

Lemma permut_Mem_split_head:
forall A l1 l2 (a: A),
  l1 *=* l2 ->
  Mem a l1 ->
  exists gh, exists gt, l2 = gh & a ++ gt.
intros; apply Mem_split; eapply Mem_permut; eauto.
Qed.

Lemma permut_dec:
forall A (a: list A) a'
  (Dec: forall k k':A, {k = k'} + {~k = k'}),
  { permut a a' } + { ~permut a a' }.
induction a; intros; destruct a'; [left | right | right |].
auto.
intro; apply permut_nil_eq in H; inversion H.
intro; symmetry in H; apply permut_nil_eq in H; inversion H.
assert (forall k k' : A, {k = k'} + {k <> k'}) as DecP by auto;
specialize Dec with a a1; destruct Dec; subst.
apply IHa with (a':=a') in DecP;
destruct DecP; [left | right]; auto;
intro; apply permut_cons_inv in H; contradiction.
(* now, if a <> a1 there's no simple way to use IHa with just a':=a *)
Admitted. (* !!! Bug: #38 *)

Close Scope permut_scope.