Require Import LLSubstitution.
Require Import PermutLib.

Open Scope is5_scope.
Open Scope labeled_is5_scope.
Open Scope permut_scope.

Fixpoint ok_Gamma (G: Context_L) (Used: list var) : Prop :=
match G with
| nil => True
| (w, (v, A)) :: G' => ~ Mem v Used /\ ok_Gamma G' (v::Used)
end.

Fixpoint ok_Omega (L: list var) : Prop :=
match L with
| nil => True
| l :: L' => ~ Mem l L' /\ ok_Omega L'
end.

Definition ok_L Omega Gamma := ok_Omega Omega /\ok_Gamma Gamma nil.

Global Reserved Notation " Omega ';' Gamma '|-' M ':::' A '@' w " (at level 70).

Inductive types_L: worlds_L -> Context_L -> te_L -> ty -> var -> Prop :=

| t_hyp_L: forall Omega Gamma v A w
  (Ok: ok_L Omega Gamma)
  (HT: Mem (w, (v, A)) Gamma),
  Omega; Gamma |- hyp_L (fte v) ::: A @ w

| t_lam_L: forall L Omega Gamma w A B M
  (Ok: ok_L Omega Gamma)
  (HT: forall x, x \notin L ->
    Omega; (w, (x,A))::Gamma |- (M ^t^ (hyp_L (fte x))) ::: B @ w),
  Omega; Gamma |- lam_L A M ::: A ---> B @ w

| t_appl_L: forall Omega Gamma w A B M N
  (Ok: ok_L Omega Gamma)
  (HT1: Omega; Gamma |- M ::: A ---> B @ w)
  (HT2: Omega; Gamma |- N ::: A @ w),
  Omega; Gamma |- appl_L M N ::: B @ w

| t_box_L: forall L Omega Gamma w M A
  (Ok: ok_L Omega Gamma)
  (HT: forall x, x \notin L ->
    (x :: Omega); Gamma |- (M ^w^ (fwo x)) ::: A @ w),
  Omega; Gamma |- box_L M ::: [*]A @ w

| t_unbox_L: forall Omega Gamma w M A
  (Ok: ok_L Omega Gamma)
  (HT: Omega; Gamma |- M ::: [*]A @ w),
  Omega; Gamma |- unbox_L M ::: A @ w

| t_fetch_L: forall Omega Gamma w w' M A
  (Ok: ok_L Omega Gamma)
  (HT: Omega; Gamma |- M ::: [*]A @ w),
  Omega; Gamma |- fetch_L (fwo w) M ::: [*]A @ w'

| t_here: forall Omega Gamma w M A
  (Ok: ok_L Omega Gamma)
  (HT: Omega; Gamma |- M ::: <*>A @ w),
  Omega; Gamma |- here_L M ::: A @ w

| t_get_L: forall Omega Gamma w w' M A
  (Ok: ok_L Omega Gamma)
  (HT: Omega; Gamma |- M ::: <*>A @ w),
  Omega; Gamma |- get_L (fwo w) M ::: <*>A @ w'

| t_letd_L: forall Lw Lt Omega Gamma w M N A B
  (Ok: ok_L Omega Gamma)
  (HT1: Omega; Gamma |- M ::: <*>A @ w)
  (HT2: forall t, t \notin Lt -> forall w', w' \notin Lw ->
    w' :: Omega; (w, (t, A)) :: Gamma |-
      ((N ^w^ (fwo w')) ^t^ (hyp_L (fte t)))  ::: B @ w),
  Omega; Gamma |-letd_L M N ::: B @ w

where " Omega ';' Gamma '|-' M ':::' A '@' w " := (types_L Omega Gamma M A w):
  labeled_is5_scope.

Inductive value_L: te_L -> Prop :=
| val_lam_L: forall A M, value_L (lam_L A M)
| val_box_L: forall M, value_L (box_L M)
| val_here_L: forall M (HT: value_L M), value_L (here_L M)
.

Global Reserved Notation " M |-> N " (at level 70).


Inductive step_LF: te_L * vwo -> te_L * vwo -> Prop :=
| red_appl_lam_L: forall A M N w,
   lc_t_L M -> lc_w_L (M ^t^ N) ->
   lc_t_L N -> lc_w_L N ->
   (appl_L (lam_L A M) N, w) |-> (M ^t^ N, w)
| red_unbox_box_L: forall M w,
   lc_t_L M -> lc_w_L (M ^w^ w) ->
   (unbox_L (box_L M), w) |-> (M ^w^ w, w)
| red_letd_here_L: forall M N w (HVal: value_L M),
   lc_t_L M -> lc_w_L M ->
   lc_t_L N ^t^ M -> lc_w_L (N ^w^ w) ->
   (letd_L (here_L M) N, w) |-> ((N ^w^ w) ^t^ M, w)
| red_appl_L: forall M N M' w (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   lc_t_L N -> lc_w_L N ->
   (appl_L M N, w) |-> (appl_L M' N, w)
| red_unbox_L: forall M M' w (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   (unbox_L M, w) |-> (unbox_L M', w)
| red_fetch_L: forall M M' w w'  (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   (fetch_L w M, w') |-> (fetch_L w M', w')
| red_fetch_val_L: forall w M w' (HVal: value_L M),
   lc_t_L M -> lc_w_L M ->
   (fetch_L w M, w') |-> ({{w'//w}}M, w')
| red_here_L: forall N N' w (HRed: (N, w) |-> (N',w)),
   lc_t_L N -> lc_w_L N ->
   (here_L N, w) |-> (here_L N', w)
| red_letd_L: forall M M' N w (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   lc_t_L (N ^t^ M) -> lc_w_L (N ^w^ w) ->
   (letd_L M N, w) |-> (letd_L M' N, w)
| red_get_L: forall w M M' w' (HRed: (M, w) |-> (M', w)),
   lc_t_L M -> lc_w_L M ->
   (get_L w M, w') |-> (get_L w M', w')
| red_get_val_L: forall w M w' (HVal: value_L M),
   lc_t_L M -> lc_w_L M ->
   (get_L w (here_L M), w') |-> (here_L {{w'//w}}M, w')
where " M |-> N " := (step_LF M N ) : labeled_is5_scope.


Lemma Progress:
forall Omega M A w
  (H_lc: lc_w_L M)
  (H_lc': lc_t_L M)
  (HProgress: Omega; nil |- M ::: A@w),
  value_L M \/ exists N, (M, fwo w) |-> (N, fwo w).
Admitted.

Lemma Preservation:
forall Omega M N A w w'
  (HType: Omega; nil |- M ::: A@w)
  (HStep: (M, fwo w) |-> (N,fwo w')),
  Omega; nil |- N ::: A@w'.
Admitted.