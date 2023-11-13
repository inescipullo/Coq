module Mirror_function2 where

import qualified Prelude

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data Bintree a =
   Empty_bintree
 | Add_bintree a (Bintree a) (Bintree a)

inverse :: (Bintree a1) -> Bintree a1
inverse t =
  case t of {
   Empty_bintree -> Empty_bintree;
   Add_bintree x l r -> Add_bintree x (inverse r) (inverse l)}

mirrorC2 :: (Bintree a1) -> (Bintree a1)
mirrorC2 =
  inverse

