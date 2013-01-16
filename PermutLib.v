Require Import Setoid.
Require Export LibListSorted.
Require Export LibList.
Require Export LibFset.
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

Lemma Mem_dec:
forall A (l: list A) e
  (Dec: forall k k':A, { k = k' } + {~ k = k'}),
  {Mem e l} + {~ Mem e l}.
induction l; intros; [ right; rewrite Mem_nil_eq; tauto | ].
assert (forall k k' : A, {k = k'} + {k <> k'}) as DecP by auto.
specialize Dec with e a; destruct Dec; subst; rewrite Mem_cons_eq.
left; left; auto.
specialize IHl with e; apply IHl in DecP; destruct DecP; [ left | right].
right; auto. intro nn; destruct nn; subst; [ elim n | contradiction]; auto.
Qed.

Lemma Mem_cons_spec:
forall (A : Type) (l: list A) (x y : A)
  (Dec: forall k k': A, {k=k'} + {~k=k'}),
  Mem x (y :: l) -> {x = y} + {Mem x l}.
intros; destruct (Mem_dec A l x); auto;
left; rewrite Mem_cons_eq in H; destruct H; auto; contradiction.
Qed.

Lemma Mem_split_spec:
forall A l (a:A)
  (Dec: forall k k': A, {k=k'} + {~k=k'}),
  Mem a l ->
  sigT (fun (hd: list A) =>
      sigT (fun (tl: list A) => l = hd & a ++ tl)).
induction l; intros.
rewrite Mem_nil_eq in H; contradiction.
apply Mem_cons_spec in H; auto;
destruct H; subst;
[exists nil; exists l; rew_app; auto | ];
apply IHl in m; auto;
destruct m as (hd, (tl, m)); subst;
exists (a::hd); exists tl; rew_app; auto.
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

Section OtherDefinition.

Variable A:Type.

Inductive Permutation : list A -> list A -> Prop :=
| perm_nil: Permutation nil nil
| perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap x y l : Permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' :
  Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Local Hint Constructors Permutation.

Theorem Permutation_refl : forall l : list A, Permutation l l.
Proof.
  induction l; constructor. exact IHl.
Qed.

Theorem Permutation_sym : forall l l' : list A, Permutation l l' ->
  Permutation l' l.
Proof.
  intros l l' Hperm; induction Hperm; auto.
  apply perm_trans with (l':=l'); assumption.
Qed.

Theorem Permutation_trans : forall l l' l'' : list A, Permutation l l' ->
  Permutation l' l'' -> Permutation l l''.
Proof.
  exact perm_trans.
Qed.

Hint Resolve Permutation_refl perm_nil perm_skip.

(* These hints do not reduce the size of the problem to solve and they
   must be used with care to avoid combinatoric explosions *)

Local Hint Resolve perm_swap perm_trans.
Local Hint Resolve Permutation_sym Permutation_trans.

(* This provides reflexivity, symmetry and transitivity and rewriting
   on morphims to come *)

Instance Permutation_Equivalence : Equivalence (Permutation) | 10 := {
  Equivalence_Reflexive := Permutation_refl ;
  Equivalence_Symmetric := Permutation_sym ;
  Equivalence_Transitive := Permutation_trans }.

Add Parametric Morphism (a:A) : (cons a)
  with signature Permutation ==> Permutation
  as Permutation_cons.
Proof.
  auto using perm_skip.
Qed.

Theorem Permutation_nil : forall (l : list A), Permutation nil l -> l = nil.
Proof.
  intros l HF.
  remember (@nil A) as m in HF.
  induction HF; discriminate || auto.
Qed.

Theorem Permutation_nil_cons : forall (l : list A) (x : A),
  ~ Permutation nil (x::l).
Proof.
  intros l x HF.
  apply Permutation_nil in HF; discriminate.
Qed.

Lemma Permutation_app_tail : forall (l l' tl : list A), Permutation l l' ->
  Permutation (l++tl) (l'++tl).
Proof.
  intros l l' tl Hperm; induction Hperm as [|x l l'|x y l|l l' l'']; rew_app;
    simpl; auto.
  eapply Permutation_trans with (l':=l'++tl); trivial.
Qed.

Lemma Permutation_app_head : forall (l tl tl' : list A), Permutation tl tl' ->
  Permutation (l++tl) (l++tl').
Proof.
  intros l tl tl' Hperm; induction l; [trivial |
    repeat rewrite <- app_comm_cons; constructor; assumption].
Qed.

Theorem Permutation_app : forall (l m l' m' : list A), Permutation l l' ->
  Permutation m m' -> Permutation (l++m) (l'++m').
Proof.
  intros l m l' m' Hpermll' Hpermmm'; induction Hpermll' as
    [|x l l'|x y l|l l' l'']; repeat rewrite <- app_comm_cons; rew_app; auto.
  apply Permutation_trans with (l' := (x :: y :: l) ++ m);
	[rew_app | ]; auto. replace (x::y::l++m') with ((x::y::l)++m') by
  (rew_app; auto);
          apply Permutation_app_head; auto.
  apply Permutation_trans with (l' := (l' ++ m')); try assumption.
  apply Permutation_app_tail; assumption.
Qed.

Add Parametric Morphism : (@append A)
  with signature Permutation ==> Permutation ==> Permutation
  as Permutation_app'.
  intros; auto using Permutation_app.
Qed.

Lemma Permutation_add_inside : forall a (l l' tl tl' : list A),
  Permutation l l' -> Permutation tl tl' ->
  Permutation (l ++ a :: tl) (l' ++ a :: tl').
Proof.
  intros; apply Permutation_app; auto.
Qed.

Theorem Permutation_app_comm : forall (l l' : list A),
  Permutation (l ++ l') (l' ++ l).
Proof.
  induction l as [|x l]; simpl; intro l'.
  rew_app; trivial.
  induction l' as [|y l']; simpl.
  rew_app; trivial.
  transitivity (x :: y :: l' ++ l).
  constructor; rew_app; apply IHl.
  transitivity (y :: x :: l' ++ l); constructor.
  transitivity (x :: l ++ l'); auto.
Qed.

Theorem Permutation_cons_app : forall (l l1 l2:list A) a,
  Permutation l (l1 ++ l2) -> Permutation (a :: l) (l1 ++ a :: l2).
Proof.
  intros l l1; revert l.
  induction l1.
  simpl.
  intros; apply perm_skip; auto.
  simpl; intros.
  transitivity (a0::a::l1++l2).
  apply perm_skip; auto.
  transitivity (a::a0::l1++l2).
  apply perm_swap; auto.
  rew_app; apply perm_skip; auto.
Qed.
Local Hint Resolve Permutation_cons_app.

Theorem Permutation_in : forall (l l' : list A) (x : A), Permutation l l' ->
  In x l -> In x l'.
Proof.
  intros l l' x Hperm; induction Hperm; simpl; tauto.
Qed.

Lemma Permutation_swap_middle:
forall l1 l2 l3 l4,
  Permutation (l1 ++ l2 ++ l3 ++ l4) (l1 ++ l3 ++ l2 ++ l4).
intros;
apply Permutation_app_head;
replace (l2 ++ l3 ++ l4) with ((l2 ++ l3) ++ l4) by (rew_app; auto);
replace (l3 ++ l2 ++ l4) with ((l3 ++ l2) ++ l4) by (rew_app; auto);
apply Permutation_app_tail;
apply Permutation_app_comm.
Qed.

Lemma Permutation_Mem:
forall (l l' : list A) (x : A), Permutation l l' -> Mem x l -> Mem x l'.
intros. induction H; auto.
rewrite Mem_cons_eq in H0; destruct H0; subst;
[apply Mem_here | rewrite Mem_cons_eq]; right; apply IHPermutation; auto.
repeat rewrite Mem_cons_eq in *; destruct H0; subst.
right; left; auto. destruct H; subst; [left | right]; auto.
Qed.

Theorem permut_equiv:
forall l1 l2,
  l1 *=* l2 <->
  Permutation l1 l2.
split; intro.
generalize dependent l2;
generalize dependent l1;
apply rtclosure_ind; intros; auto;
transitivity y; auto; inversion H; subst; apply Permutation_swap_middle.
induction H; permut_simpl; auto; transitivity l'; auto.
Qed.

Theorem Permutation_ind_bis :
 forall P : list A -> list A -> Prop,
   P nil nil ->
   (forall x l l', Permutation l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', Permutation l l' -> P l l' ->
     P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', Permutation l l' -> P l l' ->
     Permutation l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Permutation l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  intros; induction H; auto.
  apply Htrans with (x::y::l); auto.
  apply Hswap; auto.
  induction l; auto.
  apply Hskip; auto.
  apply Hskip; auto.
  induction l; auto.
  eauto.
Qed.

Ltac break_list l x l' H :=
  destruct l as [|x l']; simpl in *;
  injection H; intros; subst; clear H.

Theorem Permutation_app_inv : forall (l1 l2 l3 l4:list A) a,
  Permutation (l1++a::l2) (l3++a::l4) -> Permutation (l1++l2) (l3 ++ l4).
Proof.
  set (P l l' :=
         forall a l1 l2 l3 l4, l=l1++a::l2 -> l'=l3++a::l4 ->
           Permutation (l1++l2) (l3++l4)).
  cut (forall l l', Permutation l l' -> P l l').
  intros; apply (H _ _ H0 a); auto.
  intros; apply (Permutation_ind_bis P); unfold P; clear P;
    try clear H l l'; simpl; auto.
(* nil *)
  intros; destruct l1; simpl in *; discriminate.
  (* skip *)
  intros x l l' H IH; intros.
  break_list l1 b l1' H0; break_list l3 c l3' H1.
  auto.
  apply perm_trans with (l3'++c::l4); rew_app; auto.
  apply perm_trans with (l1'++a::l2); rew_app; auto using Permutation_cons_app.
  rew_app; apply perm_skip.
  apply (IH a l1' l2 l3' l4); auto.
  (* contradict *)
  intros x y l l' Hp IH; intros.
  break_list l1 b l1' H; break_list l3 c l3' H0; rew_app;
  auto.
  break_list l3' b l3'' H; rew_app;
  auto.
  apply perm_trans with (c::l3''++b::l4); auto.
  break_list l1' c l1'' H1; rew_app;
  auto.
  apply perm_trans with (b::l1''++c::l2); auto.
  break_list l3' d l3'' H; break_list l1' e l1'' H1; rew_app;
  auto.
  apply perm_trans with (e::a::l1''++l2); auto.
  apply perm_trans with (e::l1''++a::l2); auto.
  apply perm_trans with (d::a::l3''++l4); auto.
  apply perm_trans with (d::l3''++a::l4); auto.
  apply perm_trans with (e::d::l1''++l2); auto.
  apply perm_skip; apply perm_skip.
  apply (IH a l1'' l2 l3'' l4); auto.
  (*trans*)
  intros.
  destruct (Mem_split A l' a) as (l'1, (l'2, H6)).
    apply Permutation_Mem with (l:=a::l1++l2).
    subst; rewrite <- H; auto.
    apply Mem_here.
  apply perm_trans with (l'1++l'2).
  rew_app in *; apply (H0 _ _ _ _ _ H3 H6).
  rew_app in *; apply (H2 _ _ _ _ _ H6 H4).
Qed.

End OtherDefinition.

Lemma permut_app_inv:
forall A l1 l2 l3 l4 (a:A),
  l1 & a ++ l2 *=* l3 & a ++ l4 ->
  l1 ++ l2 *=* l3 ++ l4.
intros.
apply permut_equiv.
apply Permutation_app_inv with (a:=a).
eapply permut_equiv; rew_app in *; eauto.
Qed.

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

Lemma from_list_app:
forall A (l1: list A) l2,
  from_list (l1++l2) = from_list l1 \u from_list l2.
intro A; induction l1; intros.
rewrite from_list_nil; rewrite union_empty_l; auto.
rew_app; repeat rewrite from_list_cons; rewrite IHl1;
rewrite union_assoc; auto.
Qed.

Lemma permut_from_list:
forall A (l l': list A),
  l *=* l' ->
  forall x, x \notin (from_list l) -> x \notin (from_list l').
induction l; intros.
apply permut_nil_eq in H; subst; rewrite from_list_nil; auto.
assert (a::l *=* l') by auto;
apply permut_split_head in H; destruct H as (hd, (tl, H)); subst; simpl;
assert (l *=* hd ++ tl) by
  (apply permut_cons_inv with (a:=a); rewrite H1; permut_simpl);
apply IHl with (x:=x) in H;
repeat rewrite from_list_app in *; rewrite from_list_cons in *;
repeat rewrite notin_union in *; destruct H0; destruct H;
repeat split; try (rewrite from_list_nil; apply notin_empty); auto.
Qed.

(* This is the decidability as in DecidableEquivalence class *)
Lemma permut_Dec:
forall A (a: list A) a'
  (Dec: forall k k':A, {k = k'} + {~k = k'}),
  (permut a a') \/ (~permut a a').
induction a; intros.
destruct a'; [left | right]; auto;
intro; apply permut_nil_eq in H; inversion H.
assert ({Mem a a'} + {~ Mem a a'}) as H by (apply Mem_dec; auto);
destruct H.
(* Mem a a' *)
apply Mem_split in m; destruct m as (hd, (tl, m)).
specialize IHa with (a':=hd++tl); apply IHa in Dec; destruct Dec;
[ left | right ]; subst.
rewrite H; permut_simpl.
intro; elim H. apply permut_cons_inv with (a:=a); rewrite H0; permut_simpl.
(* ~ Mem a a' *)
right; intro;
apply permut_split_head in H; destruct H as (hd, (tl, H)); subst;
repeat rewrite Mem_app_or_eq in n; elim n; left; right; apply Mem_here.
Qed.

Lemma permut_dec:
forall A (a: list A) a'
  (Dec: forall k k':A, {k = k'} + {~k = k'}),
  { permut a a' } + { ~permut a a' }.
induction a; intros.
destruct a'; [left | right]; auto;
intro; apply permut_nil_eq in H; inversion H.
assert ({Mem a a'} + {~ Mem a a'}) as H by (apply Mem_dec; auto);
destruct H.
(* Mem a a' *)
apply Mem_split_spec in m; auto; destruct m as (hd, (tl, m)); subst.
specialize IHa with (a':=hd++tl); apply IHa in Dec; destruct Dec;
[left | right].
rewrite p; permut_simpl.
intro; elim n; apply permut_cons_inv with (a:=a).
rewrite H; permut_simpl.
(* ~ Mem a a' *)
right; intro;
apply permut_split_head in H; destruct H as (hd, (tl, H)); subst;
repeat rewrite Mem_app_or_eq in n; elim n; left; right; apply Mem_here.
Qed.

Lemma notin_Mem:
forall A (x: A) U,
  x \notin from_list U ->
  ~ Mem x U.
induction U; intros.
rewrite Mem_nil_eq; tauto.
intro Ha; rewrite Mem_cons_eq in Ha; destruct Ha;
rewrite from_list_cons in H; rewrite notin_union in H; destruct H as (H1, H2).
  subst; apply notin_same in H1; contradiction.
  apply IHU in H2; contradiction.
Qed.

Close Scope permut_scope.