Require Export Syntax.
Require Export Substitution.
Require Import FSets.
Require Import List.
Require Import Metatheory.

Open Scope is5_scope.

Global Reserved Notation " G '|=' Gamma '|-' M ':::' A " (at level 70).

Definition Context := list ty.

Definition EmptySet s := forall a:Context, a \notin s.

(* Statics *)

Inductive types: fset Context -> Context -> te -> ty -> Prop :=
| t_hyp: forall A G Gamma v_n
  (HT: nth_error Gamma v_n = Some A),
  G |= Gamma |- (hyp v_n) ::: A
| t_lam: forall A B G Gamma M 
  (HT: G |= A::Gamma |- M ::: B),
  G |= Gamma |- (lam A M) ::: A ---> B
| t_appl: forall A B G Gamma M N
  (HT1: G |= Gamma |- M ::: A ---> B)
  (HT2: G |= Gamma |- N ::: A),
  G |= Gamma |- (appl M N) ::: B
| t_box: forall A G Gamma M
  (HT: \{Gamma} \u G |= nil |- M ::: A),
  G |= Gamma |- (box M) ::: [*] A
| t_unbox: forall A G Gamma M
  (HT: G |= Gamma |- M ::: [*] A),
  G |= Gamma |- unbox M ::: A
| t_unbox_fetch: forall A G Gamma1 Gamma2 M
  (HIn: Gamma2 \in G)
  (HT: \{Gamma1} \u G \- \{Gamma2} |= Gamma2 |- M ::: [*] A),
  G |= Gamma1 |- unbox_fetch M ::: A
| t_here: forall A G Gamma M
  (HT: G |= Gamma |- M ::: A),
  G |= Gamma |- here M ::: <*> A
| t_get_here: forall A G Gamma1 Gamma2 M
  (HIn: Gamma2 \in G)
  (HT: \{Gamma1} \u G \- \{Gamma2}|= Gamma2 |- M ::: A),
  G |= Gamma1 |- get_here M ::: <*> A
| t_letdia: forall A B G Gamma M N
  (HT1: G |= Gamma |- M ::: <*> A)
  (HT2: \{A::nil} \u G |= Gamma |- N ::: B),
  G |= Gamma |- letdia M N ::: B
| t_letdia_get: forall A B G Gamma1 Gamma M N
  (HIn: Gamma \in G)
  (HT1: \{Gamma1} \u G \- \{Gamma}|= Gamma |- M ::: <*> A)
  (HT2: \{A::nil} \u G |= Gamma1 |- N ::: B),
  G |= Gamma1 |- letdia_get M N ::: B
where " G '|=' Gamma '|-' M ':::' A " := (types G Gamma M A).

(* Dynamics *)

Inductive value: te -> Prop :=
| val_lam: forall A M, value (lam A M)
| val_box: forall M, value (box M)
| val_here: forall M, value M -> value (here M)
| val_get_here: forall M, value M -> value (get_here M)
.

Global Reserved Notation " M |-> N " (at level 70).

Inductive step: te -> te -> Prop :=
| red_appl_lam: forall M A N, appl (lam A M) N |-> [N//0] M
| red_unbox_box: forall M, unbox (box M) |-> M
| red_unbox_fetch_box: forall M, unbox_fetch (box M) |-> M
| red_letdia_here: forall M N, letdia (here M) N |-> [M//0]N
| red_letdia__get_here: forall M N, letdia (get_here M) N |-> [M//0]N
| red_letdia_get__here: forall M N, letdia_get (here M) N |-> [M//0]N
| red_letdia_get_get_here: forall M N, letdia_get (get_here M) N |-> [M//0]N
| red_appl: forall M N M' (HT: M |-> M'), appl M N |-> appl M' N
| red_unbox: forall M M' (HT: M |-> M'), unbox M |-> unbox M'
| red_unbox_fetch: forall M M' (HT: M |-> M'), unbox_fetch M |-> unbox_fetch M'
| red_dia_here: forall M M' (HT: M |-> M'), here M |-> here M'
| red_dia_move: forall M M' (HT: M |-> M'), get_here M |-> get_here M'
| red_letdia: forall M N M' (HT: M |-> M'), letdia M N |-> letdia M' N
| red_letdia_move: forall M N M' (HT: M |-> M'), letdia_get M N |-> letdia_get M' N
where " M |-> N " := (step M N ) : is5_scope.

Close Scope is5_scope.