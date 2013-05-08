type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
  | O -> m
  | S p -> S (plus p m)

(** val indefinite_description : __ -> 'a1 **)

let indefinite_description =
  failwith "AXIOM TO BE REALIZED"

(** val classicT : sumbool **)

let classicT =
  let h = indefinite_description __ in
  (match h with
   | True -> Left
   | False -> Right)

type decidable =
  bool
  (* singleton inductive, whose constructor was decidable_make *)

type 'a comparable =
  'a -> 'a -> decidable
  (* singleton inductive, whose constructor was make_comparable *)

(** val nat_compare : nat -> nat -> bool **)

let rec nat_compare x y =
  match x with
  | O ->
    (match y with
     | O -> True
     | S n -> False)
  | S x' ->
    (match y with
     | O -> False
     | S y' -> nat_compare x' y')

(** val nat_comparable : nat comparable **)

let nat_comparable x y =
  nat_compare x y

(** val inhab_witness : __ -> 'a1 **)

let inhab_witness _ =
  indefinite_description __

(** val epsilon_def : __ -> 'a1 **)

let epsilon_def _ =
  match classicT with
  | Left -> indefinite_description __
  | Right -> inhab_witness __

(** val epsilon : __ -> 'a1 **)

let epsilon _ =
  epsilon_def __

(** val fold_right : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec fold_right f acc = function
| Nil -> acc
| Cons (x, l') -> f x (fold_right f acc l')

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let map f =
  fold_right (fun x acc -> Cons ((f x), acc)) Nil

(** val append : 'a1 list -> 'a1 list -> 'a1 list **)

let append l1 l2 =
  fold_right (fun x acc -> Cons (x, acc)) l2 l1

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
  type var = nat
  
  (** val var_comp : var comparable **)
  
  let var_comp =
    nat_comparable
  
  (** val var_comparable : var comparable **)
  
  let var_comparable =
    var_comp
  
  type vars = var FsetImpl.fset
  
  (** val var_gen_list : nat list -> nat **)
  
  let var_gen_list l =
    plus (S O) (fold_right plus O l)
  
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
| Bte of nat
| Fte of Variables.var

(** val shift_vte : vte -> vte **)

let shift_vte v = match v with
| Bte n -> Bte (S n)
| Fte v0 -> v

(** val eq_var_dec : Variables.var -> Variables.var -> sumbool **)

let eq_var_dec =
  failwith "AXIOM TO BE REALIZED"

(** val eq_ty_dec : ty -> ty -> sumbool **)

let rec eq_ty_dec t b0 =
  match t with
  | Tvar ->
    (match b0 with
     | Tvar -> Left
     | _ -> Right)
  | Tarrow (t0, t1) ->
    (match b0 with
     | Tarrow (t2, t3) ->
       (match eq_ty_dec t0 t2 with
        | Left -> eq_ty_dec t1 t3
        | Right -> Right)
     | _ -> Right)
  | Tbox t0 ->
    (match b0 with
     | Tbox t1 -> eq_ty_dec t0 t1
     | _ -> Right)

(** val eq_vte_dec : vte -> vte -> sumbool **)

let eq_vte_dec v1 v2 =
  match v1 with
  | Bte x ->
    (match v2 with
     | Bte n0 ->
       let rec f n n1 =
         match n with
         | O ->
           (match n1 with
            | O -> Left
            | S n2 -> Right)
         | S n2 ->
           (match n1 with
            | O -> Right
            | S n3 -> f n2 n3)
       in f x n0
     | Fte v -> Right)
  | Fte x ->
    (match v2 with
     | Bte n -> Right
     | Fte v0 -> eq_var_dec x v0)

(** val fresh : Variables.var FsetImpl.fset -> Variables.var **)

let fresh l =
  Variables.var_gen l

type ctx_LF = (Variables.var, ty) prod list

type bg_LF = ctx_LF list

type te_LF =
| Hyp_LF of vte
| Lam_LF of ty * te_LF
| Appl_LF of te_LF * te_LF
| Box_LF of te_LF
| Unbox_LF of te_LF

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

(** val mem_dec : 'a1 list -> 'a1 -> ('a1 -> 'a1 -> sumbool) -> sumbool **)

let rec mem_dec l e dec =
  match l with
  | Nil -> Right
  | Cons (y, l0) ->
    let dec0 = dec e y in
    (match dec0 with
     | Left -> Left
     | Right -> mem_dec l0 e dec)

(** val mem_cons_spec :
    'a1 list -> 'a1 -> 'a1 -> ('a1 -> 'a1 -> sumbool) -> sumbool **)

let mem_cons_spec l x y dec =
  let s = mem_dec l x in
  (match s dec with
   | Left -> Right
   | Right -> Left)

(** val subst_t_LF : te_LF -> vte -> te_LF -> te_LF **)

let rec subst_t_LF m x n = match n with
| Hyp_LF v ->
  (match eq_vte_dec x v with
   | Left -> m
   | Right -> n)
| Lam_LF (t, n') -> Lam_LF (t, (subst_t_LF m (shift_vte x) n'))
| Appl_LF (n', n'') -> Appl_LF ((subst_t_LF m x n'), (subst_t_LF m x n''))
| Box_LF n' -> Box_LF (subst_t_LF m x n')
| Unbox_LF n' -> Unbox_LF (subst_t_LF m x n')

(** val open_LF : te_LF -> te_LF -> te_LF **)

let open_LF m t =
  subst_t_LF t (Bte O) m

type pPermut_LF =
| PPermut_LF_nil
| PPermut_LF_skip of ctx_LF list * ctx_LF list
   * (Variables.var, ty) prod list * (Variables.var, ty) prod list
   * pPermut_LF
| PPermut_LF_swap of (Variables.var, ty) prod list list
   * (Variables.var, ty) prod list * (Variables.var, ty) prod list
   * (Variables.var, ty) prod list * (Variables.var, ty) prod list
| PPermut_LF_trans of ctx_LF list * ctx_LF list * ctx_LF list * pPermut_LF
   * pPermut_LF

(** val emptyEquiv_LF :
    (Variables.var, ty) prod list list -> (Variables.var, ty) prod list list **)

let rec emptyEquiv_LF = function
| Nil -> Nil
| Cons (a, g') -> Cons (Nil, (emptyEquiv_LF g'))

(** val fst_ : ('a1, 'a2) prod -> 'a1 **)

let fst_ = function
| Pair (x, y) -> x

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

type neutral_LF =
| NHyp of vte
| NAppl of te_LF * te_LF
| NUnbox of te_LF

(** val neutral_or_value : te_LF -> (neutral_LF, value_LF) sum **)

let neutral_or_value = function
| Hyp_LF v -> Inl (NHyp v)
| Lam_LF (t, t0) -> Inr (Val_lam_LF (t, t0))
| Appl_LF (t, t0) -> Inl (NAppl (t, t0))
| Box_LF t -> Inr (Val_box_LF t)
| Unbox_LF t -> Inl (NUnbox t)

(** val eq_te_LF_dec : te_LF -> te_LF -> sumbool **)

let rec eq_te_LF_dec t m0 =
  match t with
  | Hyp_LF v ->
    (match m0 with
     | Hyp_LF v0 -> eq_vte_dec v v0
     | _ -> Right)
  | Lam_LF (t0, t1) ->
    (match m0 with
     | Lam_LF (t2, t3) ->
       (match eq_ty_dec t0 t2 with
        | Left -> eq_te_LF_dec t1 t3
        | Right -> Right)
     | _ -> Right)
  | Appl_LF (t0, t1) ->
    (match m0 with
     | Appl_LF (t2, t3) ->
       (match eq_te_LF_dec t0 t2 with
        | Left -> eq_te_LF_dec t1 t3
        | Right -> Right)
     | _ -> Right)
  | Box_LF t0 ->
    (match m0 with
     | Box_LF t1 -> eq_te_LF_dec t0 t1
     | _ -> Right)
  | Unbox_LF t0 ->
    (match m0 with
     | Unbox_LF t1 -> eq_te_LF_dec t0 t1
     | _ -> Right)

type wHT =
| Val_WHT of te_LF * value_LF
| Step_WHT of te_LF * (te_LF -> step_LF -> wHT)

(** val wHT_appl : te_LF -> te_LF -> wHT -> wHT **)

let wHT_appl m n h0 =
  let t = Appl_LF (m, n) in
  let rec f t0 w n0 m0 =
    match w with
    | Val_WHT (m1, v) -> assert false (* absurd case *)
    | Step_WHT (m1, w0) ->
      let s = neutral_or_value m0 in
      (match s with
       | Inl n1 ->
         Step_WHT (m0, (fun n2 h1 ->
           let n3 = Appl_LF (n2, n0) in
           let s0 = Red_appl_LF (m0, n2, n0, h1) in f n3 (w0 n3 s0) n0 n2))
       | Inr v -> Val_WHT (m0, v))
  in f t h0 n m

(** val wHT_box : te_LF -> wHT -> wHT **)

let wHT_box m h0 =
  let t = Unbox_LF m in
  let rec f t0 w m0 =
    match w with
    | Val_WHT (m1, v) -> assert false (* absurd case *)
    | Step_WHT (m1, w0) ->
      let s = neutral_or_value m0 in
      (match s with
       | Inl n ->
         Step_WHT (m0, (fun n0 h1 ->
           let n1 = Unbox_LF n0 in
           let s0 = Red_unbox_LF (m0, n0, h1) in f n1 (w0 n1 s0) n0))
       | Inr v -> Val_WHT (m0, v))
  in f t h0 m

type red = __

(** val property_3 :
    ty -> te_LF -> neutral_LF -> (te_LF -> step_LF -> red) -> red **)

let rec property_3 t m h x =
  match t with
  | Tvar -> Obj.magic (Step_WHT (m, (Obj.magic x)))
  | Tarrow (t0, t1) ->
    Obj.magic (fun n _ hRed ->
      property_3 t1 (Appl_LF (m, n)) (NAppl (m, n)) (fun m' h0 ->
        match h0 with
        | Red_appl_LF (m0, m'0, n0, h3) -> Obj.magic x m'0 h3 n __ hRed
        | _ -> assert false (* absurd case *)))
  | Tbox t0 ->
    property_3 t0 (Unbox_LF m) (NUnbox m) (fun m' h0 ->
      match h0 with
      | Red_unbox_LF (m0, m'0, h2) -> x m'0 h2
      | _ -> assert false (* absurd case *))

(** val property_1 : ty -> te_LF -> red -> wHT **)

let property_1 a m x =
  let nn = fresh FsetImpl.empty in
  let rec f t m0 x0 =
    match t with
    | Tvar -> Obj.magic x0
    | Tarrow (t0, t1) ->
      let h = fun x1 -> NHyp x1 in
      let x1 = fun x1 ->
        property_3 t0 (Hyp_LF (Fte x1)) (h (Fte x1)) (fun m' h1 ->
          assert false (* absurd case *))
      in
      let x2 = fun x2 -> Obj.magic x0 (Hyp_LF (Fte x2)) __ (x1 x2) in
      let h1 = fun x3 -> f t1 (Appl_LF (m0, (Hyp_LF (Fte x3)))) (x2 x3) in
      wHT_appl m0 (Hyp_LF (Fte nn)) (h1 nn)
    | Tbox t0 -> wHT_box m0 (f t0 (Unbox_LF m0) x0)
  in f a m x

(** val find_var :
    ((Variables.var, ty) prod, te_LF) prod list -> Variables.var ->
    ((Variables.var, ty) prod, te_LF) prod option **)

let rec find_var l x =
  match l with
  | Nil -> None
  | Cons (p, l') ->
    let Pair (p0, m) = p in
    let Pair (v, a) = p0 in
    (match eq_var_dec x v with
     | Left -> Some (Pair ((Pair (v, a)), m))
     | Right -> find_var l' x)

(** val mem_find_var_type :
    ((Variables.var, ty) prod, te_LF) prod list -> Variables.var -> ty ->
    te_LF **)

let rec mem_find_var_type l v a =
  match l with
  | Nil -> assert false (* absurd case *)
  | Cons (y, l0) ->
    let Pair (p, t) = y in
    let Pair (v0, t0) = p in
    let h0 =
      mem_cons_spec (map fst_ l0) (Pair (v, a)) (Pair (v0, t0)) (fun k k' ->
        let Pair (x, x0) = k in
        let Pair (v1, t1) = k' in
        (match eq_var_dec x v1 with
         | Left -> eq_ty_dec x0 t1
         | Right -> Right))
    in
    let s = eq_var_dec v v0 in
    (match s with
     | Left ->
       (match h0 with
        | Left -> t
        | Right -> assert false (* absurd case *))
     | Right ->
       (match h0 with
        | Left -> assert false (* absurd case *)
        | Right -> mem_find_var_type l0 v a))

(** val sL :
    ((Variables.var, ty) prod, te_LF) prod list -> te_LF -> te_LF **)

let rec sL l m = match m with
| Hyp_LF v0 ->
  (match v0 with
   | Bte v -> m
   | Fte v ->
     let x = find_var l v in
     (match x with
      | Some p -> let Pair (p0, m0) = p in m0
      | None -> Hyp_LF (Fte v)))
| Lam_LF (a, m0) -> Lam_LF (a, (sL l m0))
| Appl_LF (m0, n) -> Appl_LF ((sL l m0), (sL l n))
| Box_LF m0 -> Box_LF (sL l m0)
| Unbox_LF m0 -> Unbox_LF (sL l m0)

(** val fV_L :
    ((Variables.var, ty) prod, te_LF) prod list -> Variables.var
    FsetImpl.fset **)

let rec fV_L = function
| Nil -> FsetImpl.empty
| Cons (p, l') ->
  let Pair (p0, m) = p in FsetImpl.union (used_vars_te_LF m) (fV_L l')

(** val sL_hyp :
    ((Variables.var, ty) prod, te_LF) prod list -> (Variables.var, ty) prod
    list list -> (Variables.var, ty) prod list -> Variables.var -> ty ->
    (Variables.var -> ty -> te_LF -> __ -> red) -> types_LF -> red **)

let sL_hyp l g gamma v a x = function
| T_hyp_LF (a0, g0, gamma0, v0) ->
  let h1 = mem_find_var_type l v a in x v a h1 __
| _ -> assert false (* absurd case *)

(** val main_theorem :
    bg_LF -> ctx_LF -> te_LF -> ty -> types_LF -> ((Variables.var, ty) prod,
    te_LF) prod list -> (Variables.var -> ty -> te_LF -> __ -> red) -> red **)

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
      main_theorem g (Cons ((Pair (h3, a)), gamma))
        (open_LF m (Hyp_LF (Fte h3))) b0 (h h3 __) (Cons ((Pair ((Pair (h3,
        a)), v)), l)) (fun a0 b1 c0 _ ->
        let h4 =
          mem_cons_spec l (Pair ((Pair (a0, b1)), c0)) (Pair ((Pair (h3, a)),
            v)) (fun k k' ->
            let Pair (p, t2) = k in
            let Pair (v0, t3) = p in
            let Pair (p0, t4) = k' in
            let Pair (v1, t5) = p0 in
            let x0 = Pair (v0, t3) in
            let p1 = Pair (v1, t5) in
            (match let Pair (v2, t6) = p1 in
                   let Pair (v3, t7) = x0 in
                   (match eq_var_dec v3 v2 with
                    | Left -> eq_ty_dec t7 t6
                    | Right -> Right) with
             | Left -> eq_te_LF_dec t2 t4
             | Right -> Right))
        in
        (match h4 with
         | Left -> x1
         | Right -> x a0 b1 c0 __))
    in
    Obj.magic (fun n _ hRed ->
      property_3 b0 (Appl_LF ((Lam_LF (a, (sL l m))), n)) (NAppl ((Lam_LF (a,
        (sL l m))), n)) (fun m' h4 ->
        match h4 with
        | Red_appl_lam_LF (m0, n0, a0) -> x1 n hRed
        | _ -> assert false (* absurd case *)))
  | T_appl_LF (a, b0, g, gamma, m, n, h1, h2) ->
    Obj.magic (fun _ l0 _ _ _ x0 ->
      main_theorem g gamma m (Tarrow (a, b0)) h1 l0 x0) __ l __ __ __ x
      (sL l n) __ (main_theorem g gamma n a h2 l x)
  | T_box_LF (g, gamma, m, a, h) ->
    property_3 a (Unbox_LF (Box_LF (sL l m))) (NUnbox (Box_LF (sL l m)))
      (fun m' h2 ->
      match h2 with
      | Red_unbox_box_LF m0 ->
        main_theorem (append g (Cons (gamma, Nil))) Nil m a h l x
      | _ -> assert false (* absurd case *))
  | T_unbox_LF (g, gamma, m, a, h) -> main_theorem g gamma m (Tbox a) h l x
  | T_unbox_fetch_LF (g, gamma, gamma', m, a, h, g', p) ->
    main_theorem (append g (Cons (gamma', Nil))) gamma m (Tbox a) h l x

(** val wHT_Lang :
    (Variables.var, ty) prod list list -> te_LF -> ty -> types_LF -> wHT **)

let wHT_Lang g m a x =
  property_1 a m
    (main_theorem (emptyEquiv_LF g) Nil m a x Nil (fun a0 b c _ ->
      assert false (* absurd case *)))

