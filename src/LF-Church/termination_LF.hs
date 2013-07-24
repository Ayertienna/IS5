{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Termination_LF where

import qualified Prelude


unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

data Option a =
   Some a
 | None

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
proj1_sig :: a1 -> a1
proj1_sig e =
  e

plus :: int -> int -> int
plus = ( + )

indefinite_description :: a1
indefinite_description =
  Prelude.error "AXIOM TO BE REALIZED"

classicT :: bool
classicT =
  case indefinite_description of {
   true -> true;
   false -> false}

type Decidable =
  bool
  -- singleton inductive, whose constructor was decidable_make
  
type Comparable a =
  a -> a -> Decidable
  -- singleton inductive, whose constructor was make_comparable
  
nat_compare :: int -> int -> bool
nat_compare x y =
  (fun zero succ n →       if n=0 then zero () else succ (n-1))
    (\_ ->
    (fun zero succ n →       if n=0 then zero () else succ (n-1))
      (\_ ->
      true)
      (\n ->
      false)
      y)
    (\x' ->
    (fun zero succ n →       if n=0 then zero () else succ (n-1))
      (\_ ->
      false)
      (\y' ->
      nat_compare x' y')
      y)
    x

nat_comparable :: Comparable int
nat_comparable x y =
  nat_compare x y

inhab_witness :: a1
inhab_witness =
  indefinite_description

epsilon_def :: a1
epsilon_def =
  case classicT of {
   true -> indefinite_description;
   false -> inhab_witness}

epsilon :: a1
epsilon =
  proj1_sig epsilon_def

fold_right :: (a1 -> a2 -> a2) -> a2 -> (list a1) -> a2
fold_right f acc l =
  case l of {
   [] -> acc;
   (::) x l' -> f x (fold_right f acc l')}

type Set a = ()

type Fset a = (Set a)

build_fset :: (Set a1)
build_fset =
  __

empty :: Fset a1
empty =
  build_fset

singleton :: a1 -> (Set a1)
singleton x =
  build_fset

union :: (Fset a1) -> (Fset a1) -> (Set a1)
union e f =
  build_fset

inter :: (Fset a1) -> (Fset a1) -> (Set a1)
inter e f =
  build_fset

remove :: (Fset a1) -> (Fset a1) -> (Set a1)
remove e f =
  build_fset

from_list :: (list a1) -> Fset a1
from_list l =
  fold_right (\x acc -> union (singleton x) acc) empty l

type Var = int

var_comp :: Comparable Var
var_comp =
  nat_comparable

var_comparable :: Comparable Var
var_comparable =
  var_comp

type Vars = Fset Var

var_gen_list :: (list int) -> int
var_gen_list l =
  plus ((fun x → x + 1) 0) (fold_right plus 0 l)

var_gen :: Vars -> Var
var_gen e =
  var_gen_list epsilon

var_fresh :: Vars -> Var
var_fresh l =
  var_gen l

data Ty =
   Tvar
 | Tarrow Ty Ty
 | Tbox Ty
 | Tdia Ty

ty_rect :: a1 -> (Ty -> a1 -> Ty -> a1 -> a1) -> (Ty -> a1 -> a1) -> (Ty ->
           a1 -> a1) -> Ty -> a1
ty_rect f f0 f1 f2 t =
  case t of {
   Tvar -> f;
   Tarrow t0 t1 -> f0 t0 (ty_rect f f0 f1 f2 t0) t1 (ty_rect f f0 f1 f2 t1);
   Tbox t0 -> f1 t0 (ty_rect f f0 f1 f2 t0);
   Tdia t0 -> f2 t0 (ty_rect f f0 f1 f2 t0)}

data Vte =
   Bte int
 | Fte Var

eq_var_dec :: Var -> Var -> bool
eq_var_dec = ( = )

type Ctx_LF = list ((*) Var Ty)

type Bg_LF = list Ctx_LF

data Te_LF =
   Hyp_LF Vte
 | Lam_LF Ty Te_LF
 | Appl_LF Te_LF Te_LF
 | Box_LF Te_LF
 | Unbox_LF Te_LF
 | Here_LF Te_LF
 | Letdia_LF Ty Te_LF Te_LF

emptyEquiv_LF :: (list (list ((*) Var Ty))) -> list (list ((*) Var Ty))
emptyEquiv_LF g =
  case g of {
   [] -> [];
   (::) a g' -> (::) [] (emptyEquiv_LF g')}

find_var :: (list ((*) ((*) Var Ty) Te_LF)) -> Var -> Option
            ((*) ((*) Var Ty) Te_LF)
find_var l x =
  case l of {
   [] -> None;
   (::) p l' ->
    case p of {
     (,) p0 m ->
      case p0 of {
       (,) v a ->
        case eq_var_dec x v of {
         true -> Some ((,) ((,) v a) m);
         false -> find_var l' x}}}}

sL :: (list ((*) ((*) Var Ty) Te_LF)) -> Te_LF -> Te_LF
sL l m =
  case m of {
   Hyp_LF v0 ->
    case v0 of {
     Bte v -> m;
     Fte v ->
      let {x = find_var l v} in
      case x of {
       Some p ->
        case p of {
         (,) p0 m0 -> m0};
       None -> Hyp_LF (Fte v)}};
   Lam_LF a m0 -> Lam_LF a (sL l m0);
   Appl_LF m0 n -> Appl_LF (sL l m0) (sL l n);
   Box_LF m0 -> Box_LF (sL l m0);
   Unbox_LF m0 -> Unbox_LF (sL l m0);
   Here_LF m0 -> Here_LF (sL l m0);
   Letdia_LF t m0 n -> Letdia_LF t (sL l m0) (sL l n)}

type WT = Te_LF

wT_here :: Te_LF -> WT -> WT
wT_here m x =
  Here_LF x

data Cont =
   IdK Ty
 | ConsU Cont Ty
 | ConsD Cont Ty Te_LF Ty Ty
 | ConsA Cont Te_LF Ty Ty

type RC = ()

type Q = Cont -> () -> () -> RC -> WT

rCIdK :: Ty -> RC
rCIdK t =
  ty_rect (unsafeCoerce (\v _ x -> x)) (\t1 iHt1 t2 iHt2 ->
    unsafeCoerce (\v _ x ->
      case x of {
       (,) w w0 -> w})) (\t0 iHt ->
    unsafeCoerce (\v _ x ->
      case x of {
       (,) w w0 -> w})) (\t0 iHt ->
    unsafeCoerce (\v _ x -> let {x0 = x (IdK t0) __ __ iHt} in wT_here v x0))
    t

main_theorem :: Bg_LF -> Ctx_LF -> Te_LF -> Ty -> (list
                ((*) ((*) Var Ty) Te_LF)) -> (Var -> Ty -> Te_LF -> () -> Q)
                -> Cont -> RC -> WT
main_theorem =
  Prelude.error "AXIOM TO BE REALIZED"

wT_Lang :: (list (list ((*) Var Ty))) -> Te_LF -> Ty -> WT
wT_Lang g m a =
  let {
   h = main_theorem (emptyEquiv_LF g) [] m a [] (\a0 b c _ -> false_rect)
         (IdK a) (rCIdK a)}
  in
  eq_rect (sL [] m) h m

