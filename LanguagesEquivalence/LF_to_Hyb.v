Add LoadPath "..".
Add LoadPath "../LabelFree/SingleUnbox".
Add LoadPath "../Hybrid".

Require Import Shared.
Require Import LabelFree.
Require Import Hybrid.
Require Import Arith.
Require Import ListLib.
Require Import Setoid.

Open Scope is5_scope.
Open Scope permut_scope.
(* FIXME: There is no labelfree is5 scope *)
Open Scope hybrid_is5_scope.

Definition LF_to_Hyb_ctx (G: bg_LF) (G': bg_Hyb) :=
  map snd_ G' *=* G /\ ok_Hyb G' nil.

Lemma LF_to_Hyb_ctx_Ok:
forall G G',
  ok_Bg_LF G -> LF_to_Hyb_ctx G G' -> ok_Bg_Hyb G'.
Admitted.

Lemma LF_to_Hyb_ctx_extend:
forall G G' w Gamma v A,
  LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
  LF_to_Hyb_ctx (((v,A)::Gamma)::G) ((w, (v,A)::Gamma)::G').
Admitted.

Add Morphism LF_to_Hyb_ctx: LF_to_Hyb_ctx_LF.
Admitted.

(* Problem: we need the rules to reflect types_LF typing trees - otherwise
how will we tell a difference between in-place unbox and context-changing one?
we either need to make sure that LF_to_Hyb_term is only between matching
terms or make a more general relation and state that there always exists
a term from Hyb that preservesd typing. Or maybe there is a function after all?
*)


Inductive LF_to_Hyb_term: var -> types_LF -> te_LF -> te_Hyb -> Prop :=
(*
| hyp_LF_Hyb:
    forall v w, LF_to_Hyb_term w (hyp_LF v) (hyp_Hyb v)
| lam_LF_Hyb:
    forall M N t w,
      LF_to_Hyb_term w M N ->
      LF_to_Hyb_term w (lam_LF t M) (lam_Hyb t N)
| appl_LF_Hyb:
    forall M M' N N' w,
      LF_to_Hyb_term w M M' ->
      LF_to_Hyb_term w N N' ->
      LF_to_Hyb_term w (appl_LF M N) (appl_Hyb M' N')
| box_LF_Hyb:
    forall L M N w,
      (forall w0, w0 \notin L -> LF_to_Hyb_term w0 M
                                                (open_w_Hyb N (fwo w0))) ->
      LF_to_Hyb_term w (box_LF M) (box_Hyb N)
*)
| unbox_LF_Hyb:
    forall M N w G Gamma A G',
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_term w (types_LF G Gamma M ([*]A)) M N ->
      LF_to_Hyb_term w (types_LF G Gamma (unbox_LF M) A)
                     (unbox_LF M) (unbox_fetch_Hyb (fwo w) N)
(*
| here_LF_Hyb:
    forall M N w w',
      LF_to_Hyb_term w M N ->
      LF_to_Hyb_term w' (here_LF M) (get_here_Hyb w N)
| letdia_LF_Hyb:
    forall M M' N N' w w',
      LF_to_Hyb_term w M M' ->
      LF_to_Hyb_term w' N N' ->
      LF_to_Hyb_term w' (letdia_LF M N) (letdia_get_Hyb w M' N')
*)
.

Lemma LF_to_Hyb_typing:
forall M_LF G_LF Gamma_LF A M_Hyb w G_Hyb,
  types_LF G_LF Gamma_LF M_LF A ->
  LF_to_Hyb_term w True M_LF M_Hyb ->
  LF_to_Hyb_ctx (Gamma_LF :: G_LF) ((w, Gamma_LF)::G_Hyb) ->
  G_Hyb |= (w, Gamma_LF) |- M_Hyb ::: A.
intros; generalize dependent w; generalize dependent G_Hyb;
generalize dependent M_Hyb; induction H;
intros M_Hyb G_Hyb w T C; intros; inversion T; subst.
constructor; auto; eapply LF_to_Hyb_ctx_Ok; eauto.


Lemma LF_to_Hyb_steps:
forall M M' N,
  steps_LF M M' ->
  LF_to_Hyb_term M N ->
  exists N',
    steps_Hyb N N' /\ LF_to_Hyb_term M' N'.

Lemma LF_to_Hyb_left_total:
forall M, exists N,
  LF_to_Hyb_term M N.


Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
