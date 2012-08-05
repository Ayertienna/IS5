Require Import Labeled.
Require Import LabelFree.
Require Import Metatheory.
Require Import LibList.
Require Import LibListSorted.

Open Scope labeled_is5_scope.
Open Scope label_free_is5_scope.

Section Contexts.

(* labeled from label-free *)
Fixpoint annotate_worlds (w: var) (L: list (var * ty)) := 
(* TODO: add explicit result type: Context_L (when possible) *)
match L with 
  | nil => nil
  | (x, T) :: L' => (x, T, w) :: annotate_worlds w L'
end.

Definition labeled_context (G: Background_LF) (Ctx:Context_LF) :=
(* TODO: again, explicit result type when possible *)
  let CtxLst := Ctx :: G in
  let Omega := map fst CtxLst in
  let Delta := flat_map (fun x => annotate_worlds (fst x) (snd x)) CtxLst in
  (Omega, Delta, fst Ctx).
Check labeled_context.

(* label-free from labeled *)
Fixpoint filter_w (L: list (var * (var * ty_L))) (e: var) :=
match L with
| nil => nil
| v :: L' => 
  If fst v = e then 
    let (x, t) := snd v in
    (x, label_free_type t) :: filter_w L' e
  else filter_w L' e
end.

Fixpoint label_free_context (Omega: list var) Gamma w : (Background_LF * Context_LF) :=
match Omega with 
| nil => (nil, (w, nil))
| w0 :: Omega' =>
  let (G, Delta) := label_free_context Omega' Gamma w in
  let curr := filter_w Gamma w in
  If w = w0 then 
  (* we assume that Delta did not result in anything interesting -- we can do this
     because every world should be only once in Omega, so w should be there once
     as well - and this means that Delta = (w, nil) *)
    (G, (w, curr))
  else
    ((w, curr) :: G, Delta)
end.

End Contexts.

(*
Section Terms.

(* FIXME: this should be ctx_L in labeled/* code *)
Definition ctx_L:=wo.

Fixpoint labeled_world (w: ctx_LF) : (ctx_L) :=
match w with
| bctx n => bwo n
| fctx w' => fwo w'
end.

Fixpoint label_free_world (w: ctx_L) : (ctx_LF) :=
match w with
| bwo n => bctx n
| fwo w' => fctx w'
end.
(*

Fixpoint labeled_var (v: var_LF) : (var_L) :=
match v with
| bvar_LF n => bvar_L n
| fvar_LF v' => fvar_L v'
end.
 
Fixpoint label_free_var (v: var_L) : (var_LF) :=
match v with
| bvar_L n => bvar_LF n
| fvar_L v' => fvar_LF v'
end.

*)

Fixpoint labeled_term (M0: te_LF) :=
match M0 with
| hyp_LF v => hyp_L 0 (* labeled_var v *)
| lam_LF A M => lam_L (labeled_type A) (labeled_term M)
| appl_LF M N => appl_L (labeled_term M) (labeled_term N)
| box_LF M => box_L (labeled_term M)
| unbox_fetch_LF w M => unbox_L (fetch_L (labeled_world w) (labeled_term M))
| get_here_LF w M => get_L (labeled_world w) (here_L (labeled_term M))
| letdia_get_LF w M N => letd_L (get_L (labeled_world w) (labeled_term M)) (labeled_term N)
end.

Fixpoint label_free_term (M0: te_L) (w: ctx_LF) :=
match M0 with
| hyp_L v => hyp_LF (bvar 0) (* label_free_var v *)
| lam_L A M => lam_LF (label_free_type A) (label_free_term M w)
| appl_L M N => appl_LF (label_free_term M w)  (label_free_term N w)
| box_L M => box_LF (label_free_term M w)
| unbox_L M => unbox_fetch_LF w (label_free_term M w)
| here_L M => get_here_LF w (label_free_term M w)
| letd_L M N => letdia_get_LF w (label_free_term M w) (label_free_term N w)
| get_L w0 M => letdia_get_LF (label_free_world w0) (label_free_term M w) 
                             (get_here_LF (label_free_world w0) (hyp_LF 0))
| fetch_L w0 M => box_LF (unbox_fetch_LF (label_free_world w0) (label_free_term M))
end.

End Terms.
*)
(*
Lemma labeled_typing:
forall G w Gamma M A Omega Delta M' A' w'
  (HT: G |= (w, Gamma) |- M ::: A)
  (H_Ctx: (Omega, Delta, w') = labeled_context G w Gamma) 
  (H_M: M' = labeled_term M)
  (H_A: A' = labeled_type A),
  Omega; Delta |- M' ::: A' @ w'.
Admitted.

Lemma label_free_typing:
forall Omega Gamma M A w G Delta M' A'
  (HT: Omega; Gamma |- M ::: A @ w)
  (H_G: permut (label_free_context Omega Gamma) (G & (w, Delta)))
  (H_M: M' = label_free_term M)
  (H_A: A' = label_free_type A),
  G |= (w, Delta) |- M' ::: A'.
Admitted.
*)
Close Scope labeled_is5_scope.
Close Scope label_free_is5_scope.