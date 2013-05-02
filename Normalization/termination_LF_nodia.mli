type __ = Obj.t

type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

val plus : nat -> nat -> nat

val indefinite_description : __ -> 'a1

val classicT : sumbool

type decidable =
  bool
  (* singleton inductive, whose constructor was decidable_make *)

type 'a comparable =
  'a -> 'a -> decidable
  (* singleton inductive, whose constructor was make_comparable *)

val nat_compare : nat -> nat -> bool

val nat_comparable : nat comparable

val inhab_witness : __ -> 'a1

val epsilon_def : __ -> 'a1

val epsilon : __ -> 'a1

val fold_right : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val append : 'a1 list -> 'a1 list -> 'a1 list

type 'a set = __

module type FsetSig = 
 sig 
  type 'x fset 
  
  val empty : 'a1 fset
  
  val singleton : 'a1 -> 'a1 fset
  
  val union : 'a1 fset -> 'a1 fset -> 'a1 fset
  
  val inter : 'a1 fset -> 'a1 fset -> 'a1 fset
  
  val remove : 'a1 fset -> 'a1 fset -> 'a1 fset
  
  val from_list : 'a1 list -> 'a1 fset
 end

module FsetImpl : 
 FsetSig

module type VariablesType = 
 sig 
  type var 
  
  val var_comp : var comparable
  
  val var_comparable : var comparable
  
  type vars = var FsetImpl.fset
  
  val var_gen : vars -> var
  
  val var_fresh : vars -> var
 end

module Variables : 
 VariablesType

type ty =
| Tvar
| Tarrow of ty * ty
| Tbox of ty

type vte =
| Bte of nat
| Fte of Variables.var

val shift_vte : vte -> vte

val eq_var_dec : Variables.var -> Variables.var -> sumbool

val eq_ty_dec : ty -> ty -> sumbool

val eq_vte_dec : vte -> vte -> sumbool

val fresh : Variables.var FsetImpl.fset -> Variables.var

type ctx_LF = (Variables.var, ty) prod list

type bg_LF = ctx_LF list

type te_LF =
| Hyp_LF of vte
| Lam_LF of ty * te_LF
| Appl_LF of te_LF * te_LF
| Box_LF of te_LF
| Unbox_LF of te_LF

val used_vars_te_LF : te_LF -> Variables.var FsetImpl.fset

val mem_dec : 'a1 list -> 'a1 -> ('a1 -> 'a1 -> sumbool) -> sumbool

val mem_cons_spec :
  'a1 list -> 'a1 -> 'a1 -> ('a1 -> 'a1 -> sumbool) -> sumbool

val subst_t_LF : te_LF -> vte -> te_LF -> te_LF

val open_LF : te_LF -> te_LF -> te_LF

val emptyEquiv_LF :
  (Variables.var, ty) prod list list -> (Variables.var, ty) prod list list

val fst_ : ('a1, 'a2) prod -> 'a1

type types_LF =
| T_hyp_LF of ty * ctx_LF list * ctx_LF * Variables.var
| T_lam_LF of Variables.var FsetImpl.fset * ty * ty * ctx_LF list * ctx_LF
   * te_LF * (Variables.var -> __ -> types_LF)
| T_appl_LF of ty * ty * ctx_LF list * ctx_LF * te_LF * te_LF * types_LF
   * types_LF
| T_box_LF of ctx_LF list * ctx_LF * te_LF * ty * types_LF
| T_unbox_LF of ctx_LF list * ctx_LF * te_LF * ty * types_LF
| T_unbox_fetch_LF of ctx_LF list * ctx_LF * ctx_LF * te_LF * ty * types_LF
   * ctx_LF list

type value_LF =
| Val_lam_LF of ty * te_LF
| Val_box_LF of te_LF

type step_LF =
| Red_appl_lam_LF of te_LF * te_LF * ty
| Red_unbox_box_LF of te_LF
| Red_appl_LF of te_LF * te_LF * te_LF * step_LF
| Red_unbox_LF of te_LF * te_LF * step_LF

type neutral_LF =
| NHyp of vte
| NAppl of te_LF * te_LF
| NUnbox of te_LF

val neutral_or_value : te_LF -> (neutral_LF, value_LF) sum

val eq_te_LF_dec : te_LF -> te_LF -> sumbool

type sN =
| Val_SN of te_LF * value_LF
| Step_SN of te_LF * (te_LF -> step_LF -> sN)

val sN_appl : te_LF -> te_LF -> sN -> sN

val sN_box : te_LF -> sN -> sN

type red = __

val property_3 :
  ty -> te_LF -> neutral_LF -> (te_LF -> step_LF -> red) -> red

val property_1 : ty -> te_LF -> red -> sN

val find_var :
  ((Variables.var, ty) prod, te_LF) prod list -> Variables.var ->
  ((Variables.var, ty) prod, te_LF) prod option

val mem_find_var_type :
  ((Variables.var, ty) prod, te_LF) prod list -> Variables.var -> ty -> te_LF

val sL : ((Variables.var, ty) prod, te_LF) prod list -> te_LF -> te_LF

val fV_L :
  ((Variables.var, ty) prod, te_LF) prod list -> Variables.var FsetImpl.fset

val sL_hyp :
  ((Variables.var, ty) prod, te_LF) prod list -> (Variables.var, ty) prod
  list list -> (Variables.var, ty) prod list -> Variables.var -> ty ->
  (Variables.var -> ty -> te_LF -> __ -> red) -> types_LF -> red

val main_theorem :
  bg_LF -> ctx_LF -> te_LF -> ty -> types_LF -> ((Variables.var, ty) prod,
  te_LF) prod list -> (Variables.var -> ty -> te_LF -> __ -> red) -> red

val sN_Lang :
  (Variables.var, ty) prod list list -> te_LF -> ty -> types_LF -> sN

