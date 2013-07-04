type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a option =
| Some of 'a
| None

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val plus : int -> int -> int **)

let rec plus = ( + )

(** val indefinite_description : __ -> 'a1 **)

let indefinite_description =
  failwith "AXIOM TO BE REALIZED"

(** val classicT : bool **)

let classicT =
  let h = indefinite_description __ in if h then true else false

type decidable =
  bool
  (* singleton inductive, whose constructor was decidable_make *)

type 'a comparable =
  'a -> 'a -> decidable
  (* singleton inductive, whose constructor was make_comparable *)

(** val nat_compare : int -> int -> bool **)

let rec nat_compare x y =
  (fun zero succ n →       if n=0 then zero () else succ (n-1))
    (fun _ ->
    (fun zero succ n →       if n=0 then zero () else succ (n-1))
      (fun _ ->
      true)
      (fun n ->
      false)
      y)
    (fun x' ->
    (fun zero succ n →       if n=0 then zero () else succ (n-1))
      (fun _ ->
      false)
      (fun y' ->
      nat_compare x' y')
      y)
    x

(** val nat_comparable : int comparable **)

let nat_comparable x y =
  nat_compare x y

(** val inhab_witness : __ -> 'a1 **)

let inhab_witness _ =
  indefinite_description __

(** val epsilon_def : __ -> 'a1 **)

let epsilon_def _ =
  if classicT then indefinite_description __ else inhab_witness __

(** val epsilon : __ -> 'a1 **)

let epsilon _ =
  epsilon_def __

(** val fold_right : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec fold_right f acc = function
| [] -> acc
| x::l' -> f x (fold_right f acc l')

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let map f =
  fold_right (fun x acc -> (f x)::acc) []

(** val append : 'a1 list -> 'a1 list -> 'a1 list **)

let append l1 l2 =
  fold_right (fun x acc -> x::acc) l2 l1

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

module FsetImpl = 
 struct 
  type 'a fset = 'a set
  
  (** val build_fset : __ -> 'a1 set **)
  
  let build_fset _ =
    __
  
  (** val empty : 'a1 fset **)
  
  let empty =
    build_fset __
  
  (** val singleton : 'a1 -> 'a1 fset **)
  
  let singleton x =
    build_fset __
  
  (** val union : 'a1 fset -> 'a1 fset -> 'a1 fset **)
  
  let union e f =
    build_fset __
  
  (** val inter : 'a1 fset -> 'a1 fset -> 'a1 set **)
  
  let inter e f =
    build_fset __
  
  (** val remove : 'a1 fset -> 'a1 fset -> 'a1 set **)
  
  let remove e f =
    build_fset __
  
  (** val from_list : 'a1 list -> 'a1 fset **)
  
  let from_list l =
    fold_right (fun x acc -> union (singleton x) acc) empty l
 end

module type VariablesType = 
 sig 
  type var 
  
  val var_comp : var comparable
  
  val var_comparable : var comparable
  
  type vars = var FsetImpl.fset
  
  val var_gen : vars -> var
  
  val var_fresh : vars -> var
 end

module Variables = 
 struct 
  type var = int
  
  (** val var_comp : var comparable **)
  
  let var_comp =
    nat_comparable
  
  (** val var_comparable : var comparable **)
  
  let var_comparable =
    var_comp
  
  type vars = var FsetImpl.fset
  
  (** val var_gen_list : int list -> int **)
  
  let var_gen_list l =
    plus ((fun x → x + 1) 0) (fold_right plus 0 l)
  
  (** val var_gen : vars -> var **)
  
  let var_gen e =
    var_gen_list (epsilon __)
  
  (** val var_fresh : vars -> var **)
  
  let var_fresh l =
    var_gen l
 end

type ty =
| Tvar
| Tarrow of ty * ty
| Tbox of ty

type vte =
| Bte of int
| Fte of Variables.var

(** val shift_vte : vte -> vte **)

let shift_vte v = match v with
| Bte n -> Bte ((fun x → x + 1) n)
| Fte v0 -> v

(** val eq_var_dec : Variables.var -> Variables.var -> bool **)

let eq_var_dec = ( = )

(** val eq_ty_dec : ty -> ty -> bool **)

let rec eq_ty_dec t b0 =
  match t with
  | Tvar ->
    (match b0 with
     | Tvar -> true
     | _ -> false)
  | Tarrow (t0, t1) ->
    (match b0 with
     | Tarrow (t2, t3) -> if eq_ty_dec t0 t2 then eq_ty_dec t1 t3 else false
     | _ -> false)
  | Tbox t0 ->
    (match b0 with
     | Tbox t1 -> eq_ty_dec t0 t1
     | _ -> false)

(** val eq_vte_dec : vte -> vte -> bool **)

let eq_vte_dec v1 v2 =
  match v1 with
  | Bte x ->
    (match v2 with
     | Bte n0 ->
       let rec f n n1 =
         (fun zero succ n →       if n=0 then zero () else succ (n-1))
           (fun _ ->
           (fun zero succ n →       if n=0 then zero () else succ (n-1))
             (fun _ ->
             true)
             (fun n2 ->
             false)
             n1)
           (fun n2 ->
           (fun zero succ n →       if n=0 then zero () else succ (n-1))
             (fun _ ->
             false)
             (fun n3 ->
             f n2 n3)
             n1)
           n
       in f x n0
     | Fte v -> false)
  | Fte x ->
    (match v2 with
     | Bte n -> false
     | Fte v0 -> eq_var_dec x v0)

(** val fresh : Variables.var FsetImpl.fset -> Variables.var **)

let fresh l =
  Variables.var_gen l

type ctx_LF = (Variables.var*ty) list

type bg_LF = ctx_LF list

type te_LF =
| Hyp_LF of vte
| Lam_LF of ty * te_LF
| Appl_LF of te_LF * te_LF
| Box_LF of te_LF
| Unbox_LF of te_LF

(** val eq_te_LF_dec : te_LF -> te_LF -> bool **)

let rec eq_te_LF_dec t m0 =
  match t with
  | Hyp_LF v ->
    (match m0 with
     | Hyp_LF v0 -> eq_vte_dec v v0
     | _ -> false)
  | Lam_LF (t0, t1) ->
    (match m0 with
     | Lam_LF (t2, t3) ->
       if eq_ty_dec t0 t2 then eq_te_LF_dec t1 t3 else false
     | _ -> false)
  | Appl_LF (t0, t1) ->
    (match m0 with
     | Appl_LF (t2, t3) ->
       if eq_te_LF_dec t0 t2 then eq_te_LF_dec t1 t3 else false
     | _ -> false)
  | Box_LF t0 ->
    (match m0 with
     | Box_LF t1 -> eq_te_LF_dec t0 t1
     | _ -> false)
  | Unbox_LF t0 ->
    (match m0 with
     | Unbox_LF t1 -> eq_te_LF_dec t0 t1
     | _ -> false)

(** val used_vars_te_LF : te_LF -> Variables.var FsetImpl.fset **)

let rec used_vars_te_LF = function
| Hyp_LF v0 ->
  (match v0 with
   | Bte n -> FsetImpl.empty
   | Fte v -> FsetImpl.singleton v)
| Lam_LF (t, m0) -> used_vars_te_LF m0
| Appl_LF (m0, n) -> FsetImpl.union (used_vars_te_LF m0) (used_vars_te_LF n)
| Box_LF m0 -> used_vars_te_LF m0
| Unbox_LF m0 -> used_vars_te_LF m0

(** val mem_dec : 'a1 list -> 'a1 -> ('a1 -> 'a1 -> bool) -> bool **)

let rec mem_dec l e dec =
  match l with
  | [] -> false
  | y::l0 -> let dec0 = dec e y in if dec0 then true else mem_dec l0 e dec

(** val mem_cons_spec :
    'a1 list -> 'a1 -> 'a1 -> ('a1 -> 'a1 -> bool) -> bool **)

let mem_cons_spec l x y dec =
  let s = mem_dec l x in if s dec then false else true

(** val subst_t_LF : te_LF -> vte -> te_LF -> te_LF **)

let rec subst_t_LF m x n = match n with
| Hyp_LF v -> if eq_vte_dec x v then m else n
| Lam_LF (t, n') -> Lam_LF (t, (subst_t_LF m (shift_vte x) n'))
| Appl_LF (n', n'') -> Appl_LF ((subst_t_LF m x n'), (subst_t_LF m x n''))
| Box_LF n' -> Box_LF (subst_t_LF m x n')
| Unbox_LF n' -> Unbox_LF (subst_t_LF m x n')

(** val open_LF : te_LF -> te_LF -> te_LF **)

let open_LF m t =
  subst_t_LF t (Bte 0) m

type pPermut_LF =
| PPermut_LF_nil
| PPermut_LF_skip of ctx_LF list * ctx_LF list * (Variables.var*ty) list
   * (Variables.var*ty) list * pPermut_LF
| PPermut_LF_swap of (Variables.var*ty) list list * (Variables.var*ty) list
   * (Variables.var*ty) list * (Variables.var*ty) list
   * (Variables.var*ty) list
| PPermut_LF_trans of ctx_LF list * ctx_LF list * ctx_LF list * pPermut_LF
   * pPermut_LF

(** val emptyEquiv_LF :
    (Variables.var*ty) list list -> (Variables.var*ty) list list **)

let rec emptyEquiv_LF = function
| [] -> []
| a::g' -> []::(emptyEquiv_LF g')

(** val fst_ : ('a1*'a2) -> 'a1 **)

let fst_ = function
| x,y -> x

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

(** val wHT_step_back : te_LF -> te_LF -> step_LF -> wHT -> wHT **)

let wHT_step_back m m' h h0 =
  Step_WHT (m,
    (match h0 with
     | Val_WHT (m0, h1) -> ExistT (m', (h1,(Single_step_LF (m, m', h))))
     | Step_WHT (m0, h1) ->
       let ExistT (x, p) = h1 in
       let v,s = p in ExistT (x, (v,(Multi_step_LF (m, m', x, h, s))))))

(** val property_1 : ty -> te_LF -> red -> wHT **)

let property_1 a m x =
  match a with
  | Tvar -> Obj.magic x
  | Tarrow (t, t0) -> let w,r = Obj.magic x in w
  | Tbox t -> let w,r = Obj.magic x in w

(** val property_3 : ty -> te_LF -> te_LF -> step_LF -> red -> red **)

let rec property_3 t m m' h x =
  match t with
  | Tvar -> Obj.magic (wHT_step_back m m' h (Obj.magic x))
  | Tarrow (t0, t1) ->
    let w,r = Obj.magic x in
    Obj.magic ((wHT_step_back m m' h w),(fun n _ x0 ->
      property_3 t1 (Appl_LF (m, n)) (Appl_LF (m', n)) (Red_appl_LF (m, m',
        n, h)) (r n __ x0)))
  | Tbox t0 ->
    let w,r = Obj.magic x in
    Obj.magic
      ((wHT_step_back m m' h w),(property_3 t0 (Unbox_LF m) (Unbox_LF m')
                                  (Red_unbox_LF (m, m', h)) r))

(** val find_var :
    ((Variables.var*ty)*te_LF) list -> Variables.var ->
    ((Variables.var*ty)*te_LF) option **)

let rec find_var l x =
  match l with
  | [] -> None
  | p::l' ->
    let p0,m = p in
    let v,a = p0 in if eq_var_dec x v then Some ((v,a),m) else find_var l' x

(** val mem_find_var_type :
    ((Variables.var*ty)*te_LF) list -> Variables.var -> ty -> te_LF **)

let rec mem_find_var_type l v a =
  match l with
  | [] -> assert false (* absurd case *)
  | y::l0 ->
    let p,t = y in
    let v0,t0 = p in
    let h0 =
      mem_cons_spec (map fst_ l0) (v,a) (v0,t0) (fun k k' ->
        let x,x0 = k in
        let v1,t1 = k' in if eq_var_dec x v1 then eq_ty_dec x0 t1 else false)
    in
    let s = eq_var_dec v v0 in
    if s
    then if h0 then t else assert false (* absurd case *)
    else if h0
         then assert false (* absurd case *)
         else mem_find_var_type l0 v a

(** val sL : ((Variables.var*ty)*te_LF) list -> te_LF -> te_LF **)

let rec sL l m = match m with
| Hyp_LF v0 ->
  (match v0 with
   | Bte v -> m
   | Fte v ->
     let x = find_var l v in
     (match x with
      | Some p -> let p0,m0 = p in m0
      | None -> Hyp_LF (Fte v)))
| Lam_LF (a, m0) -> Lam_LF (a, (sL l m0))
| Appl_LF (m0, n) -> Appl_LF ((sL l m0), (sL l n))
| Box_LF m0 -> Box_LF (sL l m0)
| Unbox_LF m0 -> Unbox_LF (sL l m0)

(** val fV_L :
    ((Variables.var*ty)*te_LF) list -> Variables.var FsetImpl.fset **)

let rec fV_L = function
| [] -> FsetImpl.empty
| p::l' -> let p0,m = p in FsetImpl.union (used_vars_te_LF m) (fV_L l')

(** val sL_hyp :
    ((Variables.var*ty)*te_LF) list -> (Variables.var*ty) list list ->
    (Variables.var*ty) list -> Variables.var -> ty -> (Variables.var -> ty ->
    te_LF -> __ -> red) -> types_LF -> red **)

let sL_hyp l g gamma v a x = function
| T_hyp_LF (a0, g0, gamma0, v0) ->
  let h1 = mem_find_var_type l v a in x v a h1 __
| _ -> assert false (* absurd case *)

(** val main_theorem :
    bg_LF -> ctx_LF -> te_LF -> ty -> types_LF -> ((Variables.var*ty)*te_LF)
    list -> (Variables.var -> ty -> te_LF -> __ -> red) -> red **)

let rec main_theorem b c t t0 t1 l x =
  match t1 with
  | T_hyp_LF (a, g, gamma, v) ->
    sL_hyp l g gamma v a x (T_hyp_LF (a, g, gamma, v))
  | T_lam_LF (l0, a, b0, g, gamma, m, h) ->
    let h3 =
      fresh
        (FsetImpl.union l0
          (FsetImpl.union (used_vars_te_LF (sL l m))
            (FsetImpl.union (FsetImpl.from_list (map fst_ (map fst_ l)))
              (fV_L l))))
    in
    let x1 = fun v x1 ->
      main_theorem g ((h3,a)::gamma) (open_LF m (Hyp_LF (Fte h3))) b0
        (h h3 __) (((h3,a),v)::l) (fun a0 b1 c0 _ ->
        let h4 =
          mem_cons_spec l ((a0,b1),c0) ((h3,a),v) (fun k k' ->
            let p,t2 = k in
            let v0,t3 = p in
            let p0,t4 = k' in
            let v1,t5 = p0 in
            let x0 = v0,t3 in
            let p1 = v1,t5 in
            if let v2,t6 = p1 in
               let v3,t7 = x0 in
               if eq_var_dec v3 v2 then eq_ty_dec t7 t6 else false
            then eq_te_LF_dec t2 t4
            else false)
        in
        if h4 then x1 else x a0 b1 c0 __)
    in
    Obj.magic ((Val_WHT ((Lam_LF (a, (sL l m))), (Val_lam_LF (a,
      (sL l m))))),(fun n _ x2 ->
      property_3 b0 (Appl_LF ((Lam_LF (a, (sL l m))), n))
        (open_LF (sL l m) n) (Red_appl_lam_LF ((sL l m), n, a)) (x1 n x2)))
  | T_appl_LF (a, b0, g, gamma, m, n, h1, h2) ->
    let x0,x1 =
      Obj.magic (fun _ l0 _ _ _ x0 ->
        main_theorem g gamma m (Tarrow (a, b0)) h1 l0 x0) __ l __ __ __ x
    in
    x1 (sL l n) __ (main_theorem g gamma n a h2 l x)
  | T_box_LF (g, gamma, m, a, h) ->
    Obj.magic ((Val_WHT ((Box_LF (sL l m)), (Val_box_LF
      (sL l m)))),(property_3 a (Unbox_LF (Box_LF (sL l m))) (sL l m)
                    (Red_unbox_box_LF (sL l m))
                    (main_theorem (append g (gamma::[])) [] m a h l x)))
  | T_unbox_LF (g, gamma, m, a, h) ->
    let x0,x1 =
      Obj.magic (fun _ l0 _ _ _ x0 ->
        main_theorem g gamma m (Tbox a) h l0 x0) __ l __ __ __ x
    in
    x1
  | T_unbox_fetch_LF (g, gamma, gamma', m, a, h, g', p) ->
    let x0,x1 =
      Obj.magic (fun _ l0 _ _ _ x0 ->
        main_theorem (append g (gamma'::[])) gamma m (Tbox a) h l0 x0) __ l
        __ __ __ x
    in
    x1

(** val termination_language :
    (Variables.var*ty) list list -> te_LF -> ty -> types_LF -> wHT **)

let termination_language g m a x =
  property_1 a m
    (main_theorem (emptyEquiv_LF g) [] m a x [] (fun a0 b c _ -> assert false
      (* absurd case *)))

