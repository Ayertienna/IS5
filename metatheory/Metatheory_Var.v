(***************************************************************************
* Representation of variables                                              *
* Arthur Charguéraud, November 2011                                        *
* based on joint work with Brian Aydemir, July 2007                        *
***************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibList LibLogic LibNat LibEpsilon.
Require Import LibSet.
Require Export Metatheory_Set.


(* ********************************************************************** *)
(** * Abstract Definition of Variables *)

Module Type VariablesType.

(** We leave the type of variables abstract. *)

Parameter var : Set.

(** This type is inhabited. *)

Parameter var_inhab : Inhab var.

(** We can build sets of variables. *)

Definition vars := fset var.

(** Finally, we have a means of generating fresh variables. *)

Parameter var_gen : vars -> var.
Parameter var_gen_spec : forall E, (var_gen E) \notin E.
Parameter var_fresh : forall (L : vars), { x : var | x \notin L }.

End VariablesType.


(* ********************************************************************** *)
(** * Concrete Implementation of Variables *)

Module Export Variables : VariablesType.

Definition var := nat.

Lemma var_inhab : Inhab var.
Proof. apply (prove_Inhab 0). Qed.

Definition vars := fset var.

Definition var_gen_list (l : list nat) :=
  1 + fold_right plus O l.

Lemma var_gen_list_spec : forall n l,
  n \in from_list l -> n < var_gen_list l.
Proof.
  unfold var_gen_list. induction l; introv I.
  rewrite from_list_nil in I. false (in_empty_elim I).
  rewrite from_list_cons in I. rew_list.
   rewrite in_union in I. destruct I as [H|H].
     rewrite in_singleton in H. subst. nat_math.
     specializes IHl H. nat_math.
Qed.

Definition var_gen (E : vars) : var :=
  var_gen_list (epsilon (fun l => E = from_list l)).

Lemma var_gen_spec : forall E, (var_gen E) \notin E.
Proof.
  intros. unfold var_gen. spec_epsilon as l.
  applys fset_finite. rewrite Hl. introv H.
  forwards M: var_gen_list_spec H. nat_math.
Qed.

Lemma var_fresh : forall (L : vars), { x : var | x \notin L }.
Proof. intros L. exists (var_gen L). apply var_gen_spec. Qed.

End Variables.


(* ********************************************************************** *)
(** ** Lists of variables of given length and given freshness *)

(** Freshness of n variables from a set L and from one another. *)

Fixpoint fresh (L : vars) (n : nat) (xs : list var) {struct xs} : Prop :=
  match xs, n with
  | nil, O => True
  | x::xs', S n' => x \notin L /\ fresh (L \u \{x}) n' xs'
  | _,_ => False
  end.

Hint Extern 1 (fresh _ _ _) => simpl.

(* It is possible to build a list of n fresh variables. *)

Lemma var_freshes : forall L n, 
  { xs : list var | fresh L n xs }.
Proof.
  intros. gen L. induction n; intros L.
  exists* (nil : list var).
  destruct (var_fresh L) as [x Fr].
   destruct (IHn (L \u \{x})) as [xs Frs].
   exists* (x::xs).
Qed.

