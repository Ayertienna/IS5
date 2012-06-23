(***************************************************************************
* Bundle of modules formal metatheory                                      *
* Arthur Charguéraud, November 2011                                        *
* based on joint work with Brian Aydemir, July 2007                        *
***************************************************************************)
Require Export 
  LibTactics LibProd LibLogic
  Metatheory_Var 
  Metatheory_Fresh 
  Metatheory_Tactics

  Metatheory_Env.

Open Scope fset_scope.

Open Scope env_scope.


(*======================================================*)
(** MISC *)

(* Due to a parsing conflict between the syntax of tactics
   and the symbol [~:] which is used to write typing judgments
   in many developments, we need to rebind a few tactics in
   a slightly different way. *)

Tactic Notation "forwards" "~:" constr(E) :=
  forwards ~ : E.
Tactic Notation "tests" "~:" constr(E) :=
  tests ~ : E.
