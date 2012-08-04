Require Export Shared.
Require Export PermutLib.
Require Export PPermutLib.

Require Import Metatheory.
Require Import LibList.
Require Import Setoid.

Open Scope permut_scope.

(*** Definitions ***)

Fixpoint ok A (G: list (var * A)) (Used: list var) : Prop :=
match G with 
| nil => True
| (w, Gamma) :: G => If Mem w Used then False else ok A G (w::Used)
end.

Definition ok_Bg (G: Background_LF) : Prop :=
ok (list (var * ty)) G nil  /\
ok (ty) (flat_map snd G) nil.

Fixpoint used_t_vars (G: Background_LF) :=
match G with
| nil => from_list nil
| (w, Gamma) :: G => from_list (map fst Gamma) \u used_t_vars G
end. 

Fixpoint used_w_vars (G: Background_LF) :=
match G with
| nil => from_list nil
| (w, Gamma) :: G => \{w} \u used_w_vars G
end. 

(*** Lemmas ***)

(* FIXME: Admitted *)
Add Morphism ok_Bg : ok_Bg_PPermut.
skip.
Qed.

Lemma ok_Bg_ppermut:
forall G G',
  G ~=~ G' ->
  ok_Bg G ->
  ok_Bg G'.
intros; rewrite <- H; auto.
Qed.

(* FIXME: Admitted *)
Lemma ok_Bg_permut:
forall G Ctx Ctx' w,
  Ctx *=* Ctx' ->
  ok_Bg ((w, Ctx) :: G) ->
  ok_Bg ((w, Ctx') :: G).
Admitted.

(* FIXME: Admitted *)
Lemma ok_Bg_permut_last:
forall G Ctx Ctx' w,
  Ctx *=* Ctx' ->
  ok_Bg (G ++ (w, Ctx) :: nil) ->
  ok_Bg (G ++ (w, Ctx') :: nil).
Admitted.

(* FIXME: Admitted *)
Lemma ok_Bg_fresh_te:
forall G Gamma v A w,
 ok_Bg ((w, Gamma) :: G) ->
 v \notin (used_t_vars ((w,Gamma)::G)) ->
 ok_Bg ((w, (v,A)::Gamma) :: G).
Admitted.

(* FIXME: Admitted *)
Lemma ok_Bg_fresh_wo:
forall G w,
 ok_Bg G ->
 w \notin (used_w_vars G) ->
 ok_Bg ((w, nil) :: G).
Admitted.

(* FIXME: Admitted *)
Lemma ok_Bg_fresh_wo_te:
forall G w v A,
 ok_Bg G ->
 w \notin (used_w_vars G) ->
 ok_Bg ((w, (v, A) :: nil) :: G).
Admitted.

Hint Resolve ok_Bg_fresh_te ok_Bg_fresh_wo ok_Bg_fresh_wo_te.

Close Scope permut_scope.