(* TODO: imports are messed up now that there's a module *) 
Require Import Syntax.
Require Import Substitution.
Require Import Metatheory.
Require Import LibList.
Require Import LibListSorted.
Require Import Arith.

Open Scope label_free_is5_scope.

Global Reserved Notation " G '|=' Ctx '|-' M ':::' A " (at level 70).

(* Statics *)

Inductive types_LF: Background_LF -> Context_LF -> te_LF -> ty_LF -> Prop :=

| t_hyp_LF: forall A G w Gamma v_n
  (HT: Nth v_n Gamma A),
  G |= (w, Gamma) |- (hyp_LF v_n) ::: A

| t_lam_LF: forall A B G w Gamma M 
  (HT: G |= (w, A::Gamma) |- M ::: B),
  G |= (w, Gamma) |- (lam_LF A M) ::: A ---> B

| t_appl_LF: forall A B G Ctx M N
  (HT1: G |= Ctx |- M ::: A ---> B)
  (HT2: G |= Ctx |- N ::: A),
  G |= Ctx |- (appl_LF M N) ::: B

| t_box_LF: forall L A G Ctx M
  (HT: forall w', w' \notin L -> 
    G & Ctx |= (w', nil) |- M ^^ (fctx w') ::: A),
  G |= Ctx |- box_LF M ::: [*] A

| t_unbox_LF: forall A G Ctx M
  (HT: G |= Ctx |- M ::: [*] A),
  G |= Ctx |- unbox_LF M ::: A

| t_unbox_fetch_LF: forall A G w Gamma Ctx' M
  (HT: G & Ctx' |= (w, Gamma) |- M ::: [*] A),
  forall G', permut (G & (w, Gamma)) G' ->
    G' |= Ctx' |- unbox_fetch_LF (fctx w) M ::: A

| t_here_LF: forall A G Ctx M
  (HT: G |= Ctx |- M ::: A),
  G |= Ctx |- here_LF M ::: <*> A

| t_get_here_LF: forall A G w Gamma Ctx' M
  (HT: G & Ctx' |= (w, Gamma) |- M ::: A),
  forall G0, permut (G & (w, Gamma)) G0 -> 
    G0 |= Ctx' |- get_here_LF (fctx w) M ::: <*> A

| t_letdia_LF: forall L A B G Ctx M N
  (HT1: G |= Ctx |- M ::: <*> A)
  (HT2: forall w', w' \notin L ->
    (w', A :: nil) :: G |= Ctx |- N ^^ (fctx w') ::: B),
  G |= Ctx |- letdia_LF M N ::: B 

| t_letdia_get_LF: forall L A B G w Gamma Ctx' M N
  (HT1: G & Ctx' |= (w, Gamma) |- M ::: <*> A)
  (HT2: forall w', w' \notin L ->
    (w', (A :: nil)) :: G & (w, Gamma) |= Ctx' |- N ^^ (fctx w') ::: B),
  forall G0, permut (G & (w, Gamma)) G0 -> 
    G0 |= Ctx' |- letdia_get_LF (fctx w) M N ::: B

where " G '|=' Ctx '|-' M ':::' A " := (types_LF G Ctx M A) : label_free_is5_scope.

(* Dynamics *)

Inductive value_LF: te_LF -> Prop :=
| val_lam_LF: forall A M, value_LF (lam_LF A M)
| val_box_LF: forall M, value_LF (box_LF M)
| val_here_LF: forall M, value_LF M -> value_LF (here_LF M)
| val_get_here_LF: forall M Ctx, value_LF M -> value_LF (get_here_LF Ctx M)
.

Global Reserved Notation " M |-> N " (at level 70).

Inductive step_LF: (te_LF * ctx_LF) -> (te_LF * ctx_LF) -> Prop :=

| red_appl_lam_LF: forall ctx M A N,
  (appl_LF (lam_LF A M) N, ctx) |-> 
    ([N // 0] M, ctx)

| red_unbox_box_LF: forall ctx M,
  (unbox_LF (box_LF M), ctx) |-> 
    (M ^^ ctx, ctx)

| red_unbox_fetch_box_LF: forall ctx ctx' M,
  (unbox_fetch_LF ctx' (box_LF M), ctx) |-> 
    (M ^^ ctx, ctx) 

| red_letdia_here_LF: forall ctx M N,
  (letdia_LF (here_LF M) N, ctx) |-> 
    ([M // 0] N ^^ ctx , ctx)

| red_letdia__get_here_LF: forall ctx ctx' M N,
  (letdia_LF (get_here_LF ctx' M) N, ctx) |-> 
    ([M // 0] N ^^ ctx, ctx)

| red_letdia_get__here_LF: forall ctx ctx' M N,
  (letdia_get_LF ctx' (here_LF M) N, ctx) |-> 
    ([M // 0] N ^^ ctx , ctx)

| red_letdia_get_get_here_LF: forall ctx ctx' ctx'' M N,
  (letdia_get_LF ctx' (get_here_LF ctx'' M) N, ctx) |-> 
    ([M // 0] N ^^ ctx , ctx)

| red_appl_LF: forall ctx M N M'
  (HT: (M, ctx) |-> (M', ctx)), 
  (appl_LF M N, ctx) |-> (appl_LF M' N, ctx)

| red_unbox_LF: forall ctx M M'
  (HT: (M, ctx) |-> (M', ctx)), 
  (unbox_LF M, ctx) |-> (unbox_LF M', ctx)

| red_unbox_fetch_LF: forall ctx' M M' ctx
  (HT: (M, ctx') |-> (M', ctx')), 
  (unbox_fetch_LF ctx' M, ctx) |-> (unbox_fetch_LF ctx' M', ctx)

| red_here_LF: forall ctx M M' 
  (HT: (M, ctx) |-> (M', ctx)), 
  (here_LF M, ctx) |-> (here_LF M', ctx)

| red_get_here_LF: forall ctx ctx' M M' 
  (HT: (M, ctx) |-> (M', ctx)), 
  (get_here_LF ctx M, ctx') |-> (get_here_LF ctx M', ctx')

| red_letdia_LF: forall ctx M N M' 
  (HT: (M, ctx) |-> (M', ctx)),
  (letdia_LF M N, ctx) |-> (letdia_LF M' N, ctx)

| red_letdia_get_LF: forall ctx ctx' M N M'
  (HT: (M, ctx) |-> (M', ctx)), 
  (letdia_get_LF ctx M N, ctx') |-> (letdia_get_LF ctx M' N, ctx')

where " M |-> N " := (step_LF M N ) : label_free_is5_scope.


Section Lemmas.

Lemma GlobalWeakening:
forall G G' Ctx Ctx' M A
  (HT: G ++ G' |= Ctx |- M ::: A),
  G & Ctx' ++ G' |= Ctx |- M ::: A.
Admitted.

Lemma WeakeningBackgroundElem:
forall G G' w Delta Delta' Ctx M A
  (HT: G & (w, Delta) ++ G' |= Ctx |- M ::: A),
  G & (w, Delta ++ Delta') ++ G' |= Ctx |- M ::: A.
Admitted.

Lemma Weakening:
forall G w Gamma Gamma' M A
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma ++ Gamma') |- M ::: A.
Admitted.


(* Original formulations of modified typing rules can be reconstructed *)
Lemma test_box:
  forall L G G' Ctx M A,
    forall w', w' \notin L -> 
      G & Ctx ++ G' |=  (w', nil) |- M^^(fctx w') ::: A ->
      G ++ G' |= Ctx |- box_LF M ::: [*]A.
Admitted.

Lemma test_unbox_fetch:
  forall G G' Ctx w' Gamma' M A,
    G & Ctx ++ G' |= (w', Gamma') |- M ::: [*] A ->
      G & (w', Gamma') ++ G' |= Ctx |- unbox_fetch_LF (fctx w') M ::: A.
Admitted.

Lemma test_get_here:
  forall G G' Ctx w' Gamma' M A,
    G & Ctx ++ G' |= (w', Gamma') |- M ::: A ->
      G & (w', Gamma') ++ G' |= Ctx |- get_here_LF (fctx w') M ::: <*> A.
Admitted.

Lemma test_letdia_get:
  forall L G G' Ctx w' Gamma' M N A B,
    G & (w', Gamma') ++ G' |= Ctx |- M ::: <*>A ->
    forall w'', w'' \notin L -> 
      (w'', (A::nil)) :: G & Ctx ++ G' |= (w', Gamma') |- N ^^ (fctx w'') ::: B ->
      G & Ctx ++ G' |= (w', Gamma') |-  letdia_get_LF (fctx w') M N ::: B.
Admitted.

(* / *)

Fixpoint emptyEquiv (G: Background_LF) : Background_LF :=
match G with
| nil => nil
| (w, a)::G => (w, nil) :: emptyEquiv G
end.

Lemma Progress:
forall G w M A
  (HT: emptyEquiv G |= (w, nil) |- M ::: A),
  value_LF M \/ exists N, (M, fctx w) |-> (N, fctx w).
Admitted.

Lemma Preservation:
forall G w M N A
  (HT: emptyEquiv G |= (w, nil) |- M ::: A)
  (HS: (M, fctx w) |-> (N, fctx w)),
  emptyEquiv G |= (w, nil) |- N ::: A.
Admitted.

End Lemmas.

Close Scope label_free_is5_scope.
