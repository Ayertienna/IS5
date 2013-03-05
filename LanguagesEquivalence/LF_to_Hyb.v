Add LoadPath "..".
Add LoadPath "../LabelFree/SingleUnbox".
Add LoadPath "../Hybrid".

Require Import Shared.
Require Import LabelFree.
Require Import Hybrid.
Require Import Arith.

Open Scope is5_scope.
Open Scope permut_scope.
(* FIXME: There is no labelfree is5 scope *)
Open Scope hybrid_is5_scope.

Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
