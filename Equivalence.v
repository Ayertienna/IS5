Add LoadPath "./labeled" as Labeled.
Add LoadPath "./label-free" as LabelFree.
Require Import Labeled.
Require Import LabelFree.
Require Import List.
Require Import FSets.
Require Import Metatheory.
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

Fixpoint give_names (G: list Context_LF) (Used: worlds_L) :=
match G with
| nil => nil
| Gamma::G' => 
  let w := var_gen Used in
    (Gamma, w) :: give_names G' (\{w} \u Used)
end.

Fixpoint find_fst_eq (L:list (Context_LF * var)) (el: Context_LF) :=
match L with
| nil => error
| (G, w) :: L' => If G = el then Some w else find_fst_eq L' el
end.

Definition annotate_worlds (p: (Context_LF * var)) :=
match p with
| (L, w) => map (fun (x: ty_LF) => (labeled_type x, fwo w)) L
end.

Definition labeled_context (G: Background_LF) (Gamma: Context_LF) : option (worlds_L * Context_L * var) :=
  let CtxLst := give_names (Gamma::G) \{} in
  let w := find_fst_eq CtxLst Gamma in
  let Omega := from_list (map snd CtxLst) in
  let Delta := flat_map annotate_worlds CtxLst in
  match w with
    | error => error (* this is never going to happen! *)
    | Some w' => Some (Omega, Delta, w')
  end.


(* Label-free from labeled *)

Fixpoint find_and_append (a: ty_L) (w:var) (res: list (list ty_LF * var)) :=
match res with
| nil => (((label_free_type a)::nil), w) :: nil
| (Gamma, w') :: res' => 
  If w = w' then ((label_free_type a)::Gamma, w') :: res' else find_and_append a w res'
end.
  
Fixpoint find_snd_eq (L:list (Context_LF * var)) (el: var) :=
match L with
| nil => error
| (G, w) :: L' => If w = el then Some G else find_snd_eq L' el
end.

Theorem eq_pair_ty_w_dec:
forall a b: list ty_LF * var, {a = b} + {a <> b}.
intros;
decide equality.
apply eq_var_dec.
decide equality.
decide equality.
Qed.

(* TODO: Result? really? *)
Fixpoint group_contexts (Omega: worlds_L) (Forgotten: worlds_L) (Gamma: Context_L) (Result : list (Context_LF * var)) :=
match Gamma with
| nil => (map (fun (x:Context_LF * var) => (rev (fst x), snd x)) Result) 
   (* should be:
      ++ generate_empty (cardinal Omega)  
      for now we will ignore fresh, unused worlds *)
| (a, fwo w)::Gamma' => let Result' := find_and_append a w Result in
    group_contexts (Omega \- \{w}) (\{w} \u Forgotten) Gamma' Result'
| _ :: Gamma' => (* we need to get rid of this case! *) group_contexts Omega Forgotten Gamma' Result
end.

Definition label_free_context (Omega: worlds_L) (Gamma: Context_L) (w: var) : option(Background_LF * Context_LF) :=
 let contexts := group_contexts Omega \{} Gamma nil in
 let Gamma' := find_snd_eq contexts w in
 match Gamma' with
 | error => error
 | Some Gamma'' => 
    let G := map fst (remove eq_pair_ty_w_dec (Gamma'', w) contexts) in
      Some (G, Gamma'')  
 end. 

Lemma labeled_context_no_error:
forall G Gamma,
  labeled_context G Gamma <> error.
Admitted.

Lemma label_free_context_no_error:
forall Omega Gamma w,
  label_free_context Omega Gamma w <> error.
Admitted.

Lemma contexts_equiv1:
forall G Gamma Omega Delta w G' Gamma'
  (HT1: labeled_context G Gamma = Some (Omega, Delta, w))
  (HT2: label_free_context Omega Delta w = Some (G', Gamma')),
    permut G G' /\
    Gamma = Gamma'.
Admitted.

Lemma contexts_equiv2:
forall Omega Gamma w G Delta Omega' Gamma' w'
  (HT1: label_free_context Omega Gamma w = Some (G, Delta))
  (HT2: labeled_context G Delta = Some (Omega', Gamma', w')),
    (forall X, X \in Omega  <-> X \in Omega') /\
    Gamma = Gamma' /\
    w = w'.
Admitted.

End Contexts.

Close Scope labeled_is5_scope.
Close Scope label_free_is5_scope.