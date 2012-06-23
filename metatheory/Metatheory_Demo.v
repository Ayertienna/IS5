(***************************************************************************
* Demos for the tactics                                                    *
* Arthur Charguéraud, November 2011                                        *
***************************************************************************)

Require Import Metatheory LibList.


(* ********************************************************************** *)
(** Demo of pick_fresh_gen *)

Ltac test_pick_fresh_filter Y :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : var => \{}) in
  pick_fresh_gen (A \u B \u C) Y.

Lemma test_pick_fresh : forall (x y z : var) (L1 L2 L3: vars), True.
Proof.
  intros. test_pick_fresh_filter k. auto.
Qed.

(** The above invokation of [pick_fresh] generates a
  variable [k] and the hypothesis
  [k \notin L1 \u L2 \u L3 \u \{x} \u \{y} \u \{z}] *)



(* ********************************************************************** *)
(** Demo for notin *)

Lemma test_notin_solve_1 : forall x E F G,
  x \notin E \u F -> x \notin G -> x \notin (E \u G).
Proof. 
  intros. dup. 
  notin_simpl. notin_solve. notin_solve.
  notin_solve.
Qed.

Lemma test_notin_solve_2 : forall x y E F G,
  x \notin E \u \{y} \u F -> x \notin G ->
  x \notin \{y} /\ y \notin \{x}.
Proof.
  split. notin_solve. notin_solve.
Qed.

Lemma test_notin_solve_3 : forall x y,
  x <> y -> x \notin \{y} /\ y \notin \{x}.
Proof.
  split. notin_solve. notin_solve.
Qed.

Lemma test_notin_false_1 : forall x y E F G,
  x \notin (E \u \{x} \u F) -> y \notin G.
Proof. 
  intros. dup 3.
    false. notin_false.
    notin_false.
    notin_false.
Qed.

Lemma test_notin_false_2 : forall x y : var,
  x <> x -> y = x.
Proof. 
  intros. notin_false.
Qed.

Lemma test_neq_solve : forall x y E F,
  x \notin (E \u \{y} \u F) -> y \notin E ->
  y <> x /\ x <> y.
Proof.
  split. notin_solve. notin_solve.
Qed.

(* ********************************************************************** *)
(** Demo for fresh *)

Lemma test_fresh_solve_1 : forall xs L1 L2 n,
  fresh (L1 \u L2) n xs -> fresh L1 n xs.
Proof. 
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_2 : forall xs L1 L2 n,
 fresh (L1 \u L2) n xs -> fresh L2 n xs.
Proof. 
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_3 : forall xs L1 L2 n,
 fresh (L1 \u L2) n xs -> fresh \{} n xs.
Proof. 
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_4 : forall xs L1 L2 n,
 fresh (L1 \u L2) n xs -> fresh L1 (length xs) xs.
Proof. 
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_5 : forall xs L1 n m,
  m = n ->
  fresh L1 m xs -> 
  fresh L1 n xs.
Proof. 
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_6 : forall xs L1 L2 n m,
  m = n ->
  fresh (L1 \u L2) n xs -> 
  fresh L1 m xs.
Proof. 
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_7 : forall xs L1 L2 n m,
  n = m ->
  fresh (L1 \u L2) n xs -> 
  fresh L1 m xs.
Proof. 
  intros. fresh_solve.
Qed.

