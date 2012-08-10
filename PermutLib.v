Require Import Setoid.
Require Export LibListSorted.
Require Import LibList.

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

(* FIXME: Admitted *)
Lemma Mem_permut:
forall A L1 L2, permut L1 L2 -> forall (x : A), Mem x L1 -> Mem x L2.
Admitted.

Lemma permut_nil_eq:
forall A L1, permut L1 (@nil A) -> L1 = nil.
Admitted.

Close Scope permut_scope.