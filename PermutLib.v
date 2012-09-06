Require Import Setoid.

Require Export LibListSorted.
Require Export LibList.

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

Lemma test1:
forall A (G G' G'': list A), G *=* G' -> G'' *=* G' -> G *=* G''.
intros; rewrite H0; auto.
Qed.

Add Parametric Morphism A (a:A) : (cons a)
  with signature @permut A ==> @permut A
  as Permut_cons.
auto.
Qed.

Lemma Permut_last:
forall (A: Type) (a:A) L L',
  L *=* L' ->
  L & a *=* L' & a.
auto.
Qed.
Hint Resolve Permut_cons Permut_last.

Add Parametric Morphism A : (@append A)
  with signature @permut A ==> @permut A ==> @permut A
  as Permut_append.
auto.
Qed.
Hint Resolve Permut_append.

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

Lemma permut_split_head:
forall A l1 l2 (a: A), (a::l1) *=* l2 ->
  exists l3, exists l4, l2 = l3 & a ++ l4.
intros; remember (a::l1) as l1';
generalize dependent l1;
generalize dependent a;
induction H; intros; subst.
exists nil; exists l1; rew_app; auto.
Admitted. (* !!! *)

Lemma permut_remove_cons:
forall A l1 l2 (a:A), (a::l1) *=* (a::l2) -> l1 *=* l2.
Admitted. (* !!! *)

Lemma Mem_permut:
forall A L1 L2, permut L1 L2 ->
  forall (x : A), Mem x L1 -> Mem x L2.
induction L1; intros.
rewrite Mem_nil_eq in H0; contradiction.
rewrite Mem_cons_eq in H0; destruct H0;
assert (a :: L1 *=* L2) as HP by auto;
apply permut_split_head in H;
destruct H as (HH, H); destruct H as (HT, H); subst.
rewrite Mem_app_or_eq; left; apply Mem_last.
apply IHL1 with (L2 := HH++HT) in H0.
rewrite Mem_app_or_eq in *; destruct H0; [left | right];
[apply Mem_app_or; left | ]; auto.
apply permut_remove_cons with (a:=a); rewrite HP;
permut_simpl.
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
intro; apply permut_remove_cons in H; contradiction.
Admitted. (* !!! #38 *)

Close Scope permut_scope.