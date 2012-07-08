Add LoadPath "./labeled" as Labeled.
Require Import Labeled.
Require Import Metatheory.
Require Import List.
Require Import Relations.

Open Scope labeled_is5_scope.

Inductive steps_n_L: nat -> te_L -> wo -> te_L -> wo -> Prop:=
| Steps0: forall M w, steps_n_L 0 M w M w
| StepsS: forall n M N N' w,
      (M, w) |-> (N, w) ->
      steps_n_L n N w N' w ->
      steps_n_L (S n) M w N' w
.

Definition normal_form (M: te_L) := value_L M.

(* Expressing that all reductions have length at most n *)
Definition strong_norm_n (M: te_L) (n: nat):=
  forall w N m,
    value_L N ->
    steps_n_L m M w N w ->
    m <= n.

Definition strong_norm (M:te_L) :=
exists n, strong_norm_n M n.

(* FIXME: do we really ignore worlds here? *)
Fixpoint Red (M: te_L) (A: ty_L) :=
match A with 
| tvar_L => strong_norm M
| tarrow_L A1 A2 =>
  forall Omega w N
    (HLc: lc_w N)
    (HT: Omega; nil |- N ::: A1 @ w)
    (HRed: Red N A1),
    Red (appl_L M N) A2
| tbox_L A1 => False
| tdia_L A1 => False
end.

Fixpoint RedCtx (L: list te_L) (D: Context_L) :=
match L, D with
| nil, nil => True
| M::L', (A, _)::D' => Red M A /\ RedCtx L' D'
| _ ,_ => False
end.

(* head expansion *)
(* FIXME: is the way we're using world here correct? *)
Theorem CR2:
forall A M M'
  (HLc: lc_w M)
  (HRed: Red M A)
  (HStep: forall w, (M, w) |-> (M', w)),
  Red M' A.
induction A; intros; simpl in *; intros.
(* base type *)
unfold strong_norm in *;
destruct HRed as (n, HRed);
unfold strong_norm_n in *;
induction n.
exists 0; intros;
inversion H0; subst; auto;
specialize HRed with (w:=w) (N:=N) (m:=S (S n));
apply HRed in H;
[ omega |
  apply StepsS with (N:=M')];
auto.
exists n; intros;
apply Le.le_S_n;
apply HRed with (w:=w) (N:=N); eauto;
econstructor; eauto.
(* arrow type *)
apply IHA2 with (M:=appl_L M N).
constructor; auto.
apply HRed with (Omega:=Omega) (w:=w); auto.
intros;
specialize HStep with w0;
constructor; auto.
(* box type *)
auto.
(* dia type *)  
auto.
Qed.

Theorem unique_normal_form:
forall Omega M A w
  (HT: Omega; nil |- M ::: A @ w),
  forall N1 N2,
    (M, fwo w) |->* (N1, fwo w) /\
    (M, fwo w) |->* (N2, fwo w)  /\
    value_L N1 /\ value_L N2 ->
      N1 = N2.
Admitted.



Theorem termination:
forall Omega M A w
  (HT: Omega; nil |- M ::: A @ w),
  exists N, (M, fwo w) |->* (N, fwo w) /\ normal_form N.
Admitted.