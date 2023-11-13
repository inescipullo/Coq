module Mirror_function where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sig_rect :: (a1 -> () -> a2) -> a1 -> a2
sig_rect f s =
  f s __

sig_rec :: (a1 -> () -> a2) -> a1 -> a2
sig_rec =
  sig_rect

data Bintree a =
   Empty_bintree
 | Add_bintree a (Bintree a) (Bintree a)

bintree_rect :: a2 -> (a1 -> (Bintree a1) -> a2 -> (Bintree a1) -> a2 -> a2)
                -> (Bintree a1) -> a2
bintree_rect f f0 b =
  case b of {
   Empty_bintree -> f;
   Add_bintree y b0 b1 ->
    f0 y b0 (bintree_rect f f0 b0) b1 (bintree_rect f f0 b1)}

bintree_rec :: a2 -> (a1 -> (Bintree a1) -> a2 -> (Bintree a1) -> a2 -> a2)
               -> (Bintree a1) -> a2
bintree_rec =
  bintree_rect

mirrorC :: (Bintree a1) -> (Bintree a1)
mirrorC t =
  bintree_rec Empty_bintree (\a _ iHt1 _ iHt2 ->
    sig_rec (sig_rec (\x _ x0 _ -> Add_bintree a x x0) iHt2) iHt1) t

