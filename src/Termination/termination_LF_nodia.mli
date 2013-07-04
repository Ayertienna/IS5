type __ = Obj.t

type 'a option =
| Some of 'a
| None

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val plus : int -> int -> int

val indefinite_description : __ -> 'a1

val classicT : bool

type decidable =
  bool
  (* singleton inductive, whose constructor was decidable_make *)

type 'a comparable =
  'a -> 'a -> decidable
  (* singleton inductive, whose constructor was make_comparable *)

val nat_compare : int -> int -> bool

val nat_comparable : int comparable

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
| Bte of int
| Fte of Variables.var

val shift_vte : vte -> vte

val eq_var_dec : Variables.var -> Variables.var -> bool

val eq_ty_dec : ty -> ty -> bool

val eq_vte_dec : vte -> vte -> bool

val fresh : Variables.var FsetImpl.fset -> Variables.var

type ctx_LF = (Variables.var*ty) list

type bg_LF = ctx_LF list

type te_LF =
| Hyp_LF of vte
| Lam_LF of ty * te_LF
| Appl_LF of te_LF * te_LF
| Box_LF of te_LF
| Unbox_LF of te_LF

val eq_te_LF_dec : te_LF -> te_LF -> bool

val used_vars_te_LF : te_LF -> Variables.var FsetImpl.fset

val mem_dec : 'a1 list -> 'a1 -> ('a1 -> 'a1 -> bool) -> bool

val mem_cons_spec : 'a1 list -> 'a1 -> 'a1 -> ('a1 -> 'a1 -> bool) -> bool

val subst_t_LF : te_LF -> vte -> te_LF -> te_LF

val open_LF : te_LF -> te_LF -> te_LF

type pPermut_LF =
| PPermut_LF_nil
| PPermut_LF_skip of ctx_LF list * ctx_LF list * (Variables.var*ty) list
   * (Variables.var*ty) list * pPermut_LF
| PPermut_LF_swap of (Variables.var*ty) list list * (Variables.var*ty) list
   * (Variables.var*ty) list * (Variables.var*ty) list
   * (Variables.var*ty) list
| PPermut_LF_trans of ctx_LF list * ctx_LF list * ctx_LF list * pPermut_LF
   * pPermut_LF

val emptyEquiv_LF :
  (Variables.var*ty) list list -> (Variables.var*ty) list list

val fst_ : ('a1*'a2) -> 'a1

type types_LF =
| T_hyp_LF of ty * ctx_LF list * ctx_LF * Variables.var
| T_lam_LF of Variables.var FsetImpl.fset * ty * ty * ctx_LF list * ctx_LF
   * te_LF * (Variables.var -> __ -> types_LF)
| T_appl_LF of ty * ty * ctx_LF list * ctx_LF * te_LF * te_LF * types_LF
   * types_LF
| T_box_LF of ctx_LF list * ctx_LF * te_LF * ty * types_LF
| T_unbox_LF of ctx_LF list * ctx_LF * te_LF * ty * types_LF
| T_unbox_fetch_LF of ctx_LF list * ctx_LF * ctx_LF * te_LF * ty * types_LF
   * ctx_LF list * pPermut_LF

type value_LF =
| Val_lam_LF of ty * te_LF
| Val_box_LF of te_LF

type step_LF =
| Red_appl_lam_LF of te_LF * te_LF * ty
| Red_unbox_box_LF of te_LF
| Red_appl_LF of te_LF * te_LF * te_LF * step_LF
| Red_unbox_LF of te_LF * te_LF * step_LF

type steps_LF =
| Single_step_LF of te_LF * te_LF * step_LF
| Multi_step_LF of te_LF * te_LF * te_LF * step_LF * steps_LF

type wHT =
| Val_WHT of te_LF * value_LF
| Step_WHT of te_LF * (te_LF, value_LF*steps_LF) sigT

type red = __

val wHT_step_back : te_LF -> te_LF -> step_LF -> wHT -> wHT

val property_1 : ty -> te_LF -> red -> wHT

val property_3 : ty -> te_LF -> te_LF -> step_LF -> red -> red

val find_var :
  ((Variables.var*ty)*te_LF) list -> Variables.var ->
  ((Variables.var*ty)*te_LF) option

val mem_find_var_type :
  ((Variables.var*ty)*te_LF) list -> Variables.var -> ty -> te_LF

val sL : ((Variables.var*ty)*te_LF) list -> te_LF -> te_LF

val fV_L : ((Variables.var*ty)*te_LF) list -> Variables.var FsetImpl.fset

val sL_hyp :
  ((Variables.var*ty)*te_LF) list -> (Variables.var*ty) list list ->
  (Variables.var*ty) list -> Variables.var -> ty -> (Variables.var -> ty ->
  te_LF -> __ -> red) -> types_LF -> red

val main_theorem :
  bg_LF -> ctx_LF -> te_LF -> ty -> types_LF -> ((Variables.var*ty)*te_LF)
  list -> (Variables.var -> ty -> te_LF -> __ -> red) -> red

val termination_language :
  (Variables.var*ty) list list -> te_LF -> ty -> types_LF -> wHT

