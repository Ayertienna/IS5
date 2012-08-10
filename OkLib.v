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

Lemma ok_Bg_cons_last:
forall G a,
  ok_Bg (G & a) <-> ok_Bg (a :: G).
Admitted.

Lemma ok_Bg_swap:
forall C C' G,
  ok_Bg (C :: G & C') ->
  ok_Bg (C' :: G & C).
Admitted.

Hint Resolve ok_Bg_cons_last ok_Bg_swap ok_Bg_permut_last.
Hint Resolve ok_Bg_fresh_te ok_Bg_fresh_wo ok_Bg_fresh_wo_te.

Lemma ok_Bg_permut_first_tail:
forall G C C' w x A,
  ok_Bg ((w, C) :: G) ->
  C *=* (x,A)::C' ->
  ok_Bg ((w, C') :: G).
Admitted.
Hint Resolve ok_Bg_permut_first_tail.

Lemma ok_Bg_empty_first:
forall w G Gamma,
  ok_Bg ((w,Gamma) :: G) ->
  ok_Bg ((w, nil) :: G).
Admitted.

Hint Resolve ok_Bg_empty_first.

Lemma ok_Bg_Mem_eq:
forall w C C' v A A0 G,
  ok_Bg ((w, C) :: G) ->
  C *=* (v, A) :: C' ->
  Mem (v, A0) C ->
  A0 = A.
Admitted.

Lemma ok_Bg_Mem_contradict:
forall A A' w w' v C C' G G',
 ok_Bg ((w, C) :: G) ->
 Mem (v, A) C ->
 G ~=~ G' & (w', (v, A') :: C') ->
 False.
Admitted.

Lemma ok_Bg_permut_no_last:
forall G w C v A,
  ok_Bg (G & (w, (v,A) :: C)) ->
  ok_Bg (G & (w, C)).
Admitted.

Lemma ok_Bg_permut_no_last_spec:
forall G w C C0 v A,
  ok_Bg (C0::G & (w, (v,A) :: C)) ->
  ok_Bg (C0::G & (w, C)).
Admitted.

Lemma ok_Bg_no_last:
forall G w C,
  ok_Bg (G & (w,C)) ->
  ok_Bg G.
Admitted.
Hint Resolve ok_Bg_no_last.

Lemma ok_Bg_permut_no_last_spec2:
forall G w C C0 v A,
  ok_Bg (G & (w, (v,A) :: C) & C0) ->
  ok_Bg (G & (w, C) & C0).
Admitted.

Lemma ok_Bg_first_last_neq:
forall w w' C C' G,
  ok_Bg ((w, C) :: G & (w', C')) ->
  w <> w'.
Admitted.

Lemma ok_Bg_last_last2_neq:
forall w w' C C' G,
  ok_Bg (G & (w, C) & (w', C')) ->
  w <> w'.
Admitted.

Lemma ok_Bg_swap_worlds:
forall G w w' C C',
  ok_Bg (G & (w, C) & (w', C')) ->
  ok_Bg (G & (w', C) & (w, C')).
Admitted.

Lemma ok_Bg_impl_ppermut:
forall G G' w C C',
  ok_Bg ((w, C) :: G) ->
  G & (w, C) ~=~ G' & (w, C') ->
  G ~=~ G' /\ C *=* C'.
Admitted.

Lemma ok_Bg_split1:
forall G w w' C C',
  ok_Bg ((w,C)::G & (w',C')) ->
  ok_Bg ((w, C ++ C') :: G).
Admitted.

Lemma ok_Bg_split2:
forall G w w' C C',
  ok_Bg ((w,C)::G & (w',C')) ->
  ok_Bg ((w', C' ++ C) :: G).
Admitted.

Lemma ok_Bg_split3:
forall G w w' w'' C C' C'',
  ok_Bg ((w,C)::G & (w',C') & (w'',C'')) ->
  ok_Bg ((w, C) :: G & (w', C' ++ C'')).
Admitted.

Lemma ok_Bg_split4:
forall G w w' C C',
  ok_Bg (G & (w, C) & (w', C')) ->
  ok_Bg (G & (w', C' ++ C)).
Admitted.

Lemma ok_Bg_split5:
forall G w w' C C',
  ok_Bg (G & (w, C) & (w', C')) ->
  ok_Bg (G & (w, C ++ C')).
Admitted.

Lemma ok_Bg_split6:
forall G w C C' C'' w' w'',
  ok_Bg (G & (w, C) & (w', C') & (w'', C'')) ->
  ok_Bg (G & (w, C ++ C') & (w'', C'')).
Admitted.

Lemma ok_Bg_split7:
forall G w w' w'' C C' C'',
  ok_Bg ((w,C)::G & (w'',C'')) ->
  ok_Bg ((w, C ++ C'') :: G & (w', C')).
Admitted.

Lemma ok_Bg_split8:
forall G G' w w' w'' C C' C'',
  ok_Bg (G ++ G' ++ (w, C) :: (w', C') :: (w'', C'') :: nil) ->
  ok_Bg (G ++ G' ++ (w', C') :: (w'', C'' ++ C)::nil) .
Admitted.

Lemma ok_Bg_split9:
forall G w w' w'' C C' C'',
  ok_Bg ((w,C)::G & (w',C') & (w'',C'')) ->
  ok_Bg ((w, C++C') :: G & (w'', C'')).
Admitted.

Lemma ok_Bg_split10:
forall G G' w1 w2 w3 w4 c1 c2 c3 c4,
  ok_Bg (G ++ (w1, c1)::G' ++ (w2, c2) :: (w3, c3) :: (w4, c4) :: nil) ->
  ok_Bg (G ++ (w1, c1)::G' ++ (w2, c2 ++ c3) :: (w4, c4) :: nil).
Admitted.

Hint Resolve ok_Bg_split1 ok_Bg_split2 ok_Bg_split3 ok_Bg_split4 ok_Bg_split5 ok_Bg_split6 ok_Bg_split7 ok_Bg_split8 ok_Bg_split9 ok_Bg_split10.
Hint Resolve ok_Bg_permut_no_last ok_Bg_permut_no_last_spec2 ok_Bg_permut_no_last_spec ok_Bg_first_last_neq ok_Bg_last_last2_neq ok_Bg_swap_worlds. 


Close Scope permut_scope.