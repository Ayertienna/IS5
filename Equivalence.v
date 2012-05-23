Add LoadPath "./labeled" as Labeled.
Add LoadPath "./label-free" as LabelFree.
Require Import Labeled.
Require Import LabelFree.
Require Import Metatheory.
Require Import LibList.
Require Import LibListSorted.

Open Scope labeled_is5_scope.
Open Scope label_free_is5_scope.

Section Types.

Fixpoint labeled_type (A: ty_LF) : ty_L :=
match A with
| tvar_LF => tvar_L
| tarrow_LF A' A'' => tarrow_L (labeled_type A') (labeled_type A'')
| tbox_LF A' => tbox_L (labeled_type A')
| tdia_LF A' => tdia_L (labeled_type A')
end.

Fixpoint label_free_type (A: ty_L) : ty_LF :=
match A with
| tvar_L => tvar_LF
| tarrow_L A' A'' => tarrow_LF (label_free_type A') (label_free_type A'')
| tbox_L A' => tbox_LF (label_free_type A')
| tdia_L A' => tdia_LF (label_free_type A')
end.

Lemma types_id1:
forall A: ty_L,
  labeled_type ( label_free_type A )  = A.
intros;
induction A; simpl.
  reflexivity.
  rewrite IHA1; rewrite IHA2; reflexivity.
  rewrite IHA; reflexivity.
  rewrite IHA; reflexivity.
Qed.

Lemma types_id2:
forall A: ty_LF,
  label_free_type ( labeled_type A )  = A.
intros;
induction A; simpl.
  reflexivity.
  rewrite IHA1; rewrite IHA2; reflexivity.
  rewrite IHA; reflexivity.
  rewrite IHA; reflexivity.
Qed.

End Types.

Section Contexts.

(* Labeled from label-free *)

Definition annotate_worlds (p: Context_LF) : Context_L :=
match p with
| (w, L) => map (fun (x: ty_LF) => (labeled_type x, fwo w)) L
end.

Definition labeled_context (G: Background_LF) w Gamma : (worlds_L * Context_L * var) :=
  let CtxLst := (w, Gamma) :: G in
  let Omega := from_list (map fst CtxLst) in
  let Delta := flat_map annotate_worlds CtxLst in
  (Omega, Delta, w).

(* Label-free from labeled *)

Fixpoint find_and_append (a: ty_L) (w:var) (res: Background_LF) :=
match res with
| nil => (w, (label_free_type a)::nil) :: nil
| (w', Gamma) :: res' => 
  if (eq_var_dec w w') then (w', (label_free_type a)::Gamma) :: res' else find_and_append a w res'
end.

Fixpoint group_contexts (Omega: worlds_L) (Forgotten: worlds_L) (Gamma: Context_L) (Groups : Background_LF) :=
match Gamma with
| nil => (map (fun (x: Context_LF) => (fst x, rev (snd x))) Groups) 
   (* TODO: should be with ++ generate_empty (cardinal Omega)  
      for now we just ignore fresh, unused worlds - since there is no way
      (that I could find) to determine the size of an fset from Metatheory package *)
| (a, fwo w)::Gamma' => let Groups' := find_and_append a w Groups in
    group_contexts (Omega \- \{w}) (\{w} \u Forgotten) Gamma' Groups'
(* TODO: Why do we even allow Gamma to contain bound worlds? *) 
| _ :: Gamma' => group_contexts Omega Forgotten Gamma' Groups
end.

Definition label_free_context (Omega: worlds_L) (Gamma: Context_L) : Background_LF :=
  group_contexts Omega \{} Gamma nil.

(* TODO: These lemmas are not yet true, as we do not rewrite empty contexts correctly *) 
Lemma contexts_equiv1:
forall G w Gamma Omega Delta w' G'
  (HT1: labeled_context G w Gamma = (Omega, Delta, w'))
  (HT2: label_free_context Omega Delta  = G'),
    permut ((w, Gamma)::G) G'.
Admitted.

Lemma contexts_equiv2:
forall Omega Gamma G w Delta Omega' Gamma' w'
  (HT1: label_free_context Omega Gamma = G)
  (HT2: labeled_context G w Delta = (Omega', Gamma', w')),
    (forall X, X \in Omega  <-> X \in Omega') /\
    permut Gamma Gamma' /\ (* TODO: can we do better? should we? *)
    w = w'.
Admitted.

End Contexts.

Section Terms.

Fixpoint labeled_world (w: ctx_LF) : (wo) :=
match w with
| bctx n => bwo n
| fctx w' => fwo w'
end.

Fixpoint label_free_world (w: wo) : (ctx_LF) :=
match w with
| bwo n => bctx n
| fwo w' => fctx w'
end.

Fixpoint labeled_term (M0: te_LF) :=
match M0 with
| hyp_LF n => hyp_L n (* recalculate.... *)
| lam_LF A M => lam_L (labeled_type A) (labeled_term M)
| appl_LF M N => appl_L (labeled_term M) (labeled_term N)
| box_LF M => box_L (labeled_term M)
| unbox_LF M => unbox_L (labeled_term M)
| unbox_fetch_LF w M => unbox_L (fetch_L (labeled_world w) (labeled_term M))
| here_LF M => here_L (labeled_term M)
| get_here_LF w M => get_L (labeled_world w) (here_L (labeled_term M))
| letdia_LF M N => letd_L (labeled_term M) (labeled_term N)
| letdia_get_LF w M N => letd_L (get_L (labeled_world w) (labeled_term M)) (labeled_term N)
end.

Fixpoint label_free_term (M0: te_L) :=
match M0 with
| hyp_L n => hyp_LF n (* recalculate .. *)
| lam_L A M => lam_LF (label_free_type A) (label_free_term M)
| appl_L M N => appl_LF (label_free_term M)  (label_free_term N)
| box_L M => box_LF (label_free_term M)
| unbox_L M => unbox_LF (label_free_term M)
| here_L M => here_LF (label_free_term M)
| letd_L M N => letdia_LF (label_free_term M) (label_free_term N)
| get_L w M => letdia_get_LF (label_free_world w) (label_free_term M) 
                             (get_here_LF (label_free_world w) (hyp_LF 0))
| fetch_L w M => box_LF (unbox_fetch_LF (label_free_world w) (label_free_term M))
end.

End Terms.

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

Close Scope labeled_is5_scope.
Close Scope label_free_is5_scope.