{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE EmptyDataDecls #-}

-- GHC wrongly complains about pattern completeness
{-# OPTIONS -fno-warn-incomplete-patterns #-}

module Control.Applicative.GeneriFix (
    (:::)
  , TNil
  , Phantom(Whoo)
  , Phantom1(Whoo1)
  , ListU(TNil, (:::))
  , nafix
  , nafix2
  , nafix3
  , WrapTArrD(Wrap)
  , TArrD
  , TProd (MkCProd, MkNilProd)
  , projTProd
  , TElem(THere, TThere)
  , Zero
  , Succ
  ) where

-- This code would benefit from some of the PolyKinds additions, but we are avoiding it
-- until it stabilises a bit further. GHC Trac issue 5802 is a notable blocker.

import Control.Applicative.Fix
import Data.Type.Equality

data Zero
data Succ n

type family Plus a b
type instance Plus Zero b = b
type instance Plus (Succ a) b = Succ (Plus a b)

-- Indexed universe for natural number types
data NatU t where
  Zero :: NatU Zero
  Succ :: NatU ix -> NatU (Succ ix)

-- "prove" simple property about plus...
succPlus :: NatU a -> NatU b -> a :+: (Succ b) :=: Succ (a :+: b)
succPlus Zero _b = Refl
succPlus (Succ a) b = cong $ succPlus a b

plusRightZero :: NatU a -> a :+: Zero :=: a
plusRightZero Zero = Refl
plusRightZero (Succ a) = cong $ plusRightZero a

-- withTypeLevelNat :: Integer -> (forall n. NatU n -> r) -> r
-- withTypeLevelNat 0 k = k Zero
-- withTypeLevelNat n k = withTypeLevelNat (n-1) $ k . Succ

type a :+: b = Plus a b



data Phantom t = Whoo
data Phantom1 (t :: * -> *) = Whoo1



infixr 5 :::

-- type level lists of types
data TNil
data t ::: ts

-- delete type from type list at index
type family Delete ix ts
type instance Delete Zero (t ::: ts) = ts
type instance Delete (Succ ix) (t ::: ts) = t ::: (Delete ix ts)

-- concatenation
type family ts1 :++: ts2
type instance TNil :++: ts2 = ts2
type instance (t ::: ts1) :++: ts2 = t ::: (ts1 :++: ts2)

-- length
type family TLength ts
type instance TLength TNil = Zero
type instance TLength (t ::: ts) = Succ (TLength ts)

-- replicate
type family TReplicate n t 
type instance TReplicate Zero t = TNil
type instance TReplicate (Succ n) t = t ::: TReplicate n t

-- swapping two elements of a type list
type family Swap ix ts
type instance Swap Zero (t1 ::: (t2 ::: ts)) = t2 ::: (t1 ::: ts)
type instance Swap (Succ ix) (t ::: ts) = t ::: (Swap ix ts)

type family TTuple (f :: * -> *) ts
type instance TTuple f TNil = ()
type instance TTuple f (t ::: ts) = (f t, TTuple f ts)

-- Data.Type.Equality.cong doesn't work well for type families because they're not injective...
congSwap :: ix1 :=: ix2 -> ts1 :=: ts2 -> Swap ix1 ts1 :=: Swap ix2 ts2
congSwap Refl Refl = Refl




-- indexed universe for type lists
data ListU ts where
  TNil :: ListU TNil
  (:::) :: Phantom t -> ListU ts -> ListU (t ::: ts)

-- replicateTList :: NatU n -> Phantom t -> ListU (TReplicate n t)
-- replicateTList Zero _ = TNil
-- replicateTList (Succ n) t = t ::: replicateTList n t

-- GHC 7.0.4 wrongly complains that patterns are non-exhaustive..
deleteList :: TElem ix t ts -> ListU ts -> ListU (Delete ix ts)
deleteList THere (_t ::: ts) = ts
deleteList (TThere loc) (t ::: ts) = t ::: deleteList loc ts

-- GHC 7.0.4 wrongly complains that patterns are non-exhaustive..
listSwap :: Swappable ix nts -> ListU nts -> ListU (Swap ix nts)
listSwap HereSwappable (t1 ::: t2 ::: ts) = t2 ::: t1 ::: ts
listSwap (ThereSwappable swappable) (t ::: ts) = t ::: listSwap swappable ts


-- product of a list of types, under a monadic type constructor
data TProd (f :: * -> *) ts where
  MkNilProd :: TProd f TNil
  MkCProd :: f t -> TProd f ts -> TProd f (t ::: ts)

liftATProd :: (forall a. f a -> g a) -> ListU ts -> TProd f ts -> TProd g ts
liftATProd _ TNil _ = MkNilProd
liftATProd f (_t ::: tc) (MkCProd v vs) = MkCProd (f v) $ liftATProd f tc vs

-- prodReplicate :: NatU n -> TProd f (TReplicate n t) -> [f t]
-- prodReplicate = prodAllTs . replicateAllTs

-- replicateT :: NatU n -> f t -> TProd f (TReplicate n t)
-- replicateT Zero _ = MkNilProd
-- replicateT (Succ n) v = MkCProd v $ replicateT n v


-- functions with a list of types as assumptions in a monadic functor f
type TArr f asmpts t = TProd f asmpts -> t
type TArrs f asmpts results = TProd f asmpts -> TProd f results

projDelete :: TElem ix t ts -> TArrs f ts (Delete ix ts)
projDelete THere (MkCProd _ vs) = vs
projDelete (TThere loc) (MkCProd v vs) = MkCProd v $ projDelete loc vs

arrsDelete :: TElem ix t res -> TArrs f asmpts res -> TArrs f asmpts (Delete ix res)
arrsDelete loc fs = projDelete loc . fs


-- elementOf proof
data TElem ix t ts where
  THere :: TElem Zero t (t ::: ts)
  TThere :: TElem ix t ts -> TElem (Succ ix) t (t2 ::: ts)

-- indexing products of type lists
projTProd :: TElem ix t ts -> TProd f ts -> f t
projTProd THere (MkCProd v _vs) = v
projTProd (TThere loc) (MkCProd _v vs) = projTProd loc vs

arrsIndex :: TElem ix t res -> TArrs f asmpts res -> TArr f asmpts (f t)
arrsIndex loc fs = projTProd loc . fs

-- tabulate a function over a list of types to get a product of values
tabulate :: ListU ts -> (forall t ix. Phantom t -> TElem ix t ts -> f t) -> TProd f ts
tabulate TNil _vf = MkNilProd
tabulate (t ::: ts) vf = MkCProd (vf t THere) $ tabulate ts (\t' tints -> vf t' (TThere tints))

-- invertElemReplicate :: NatU n -> TElem ix t_ (TReplicate n t) -> t :=: t_
-- invertElemReplicate = invertElemAllTs . replicateAllTs


-- lists containing only one type
-- data AllTs t ts where
--   NilAllTs :: AllTs t TNil
--   ConsAllTs :: AllTs t ts -> AllTs t (t ::: ts)

-- replicateAllTs :: NatU n -> AllTs t (TReplicate n t)
-- replicateAllTs Zero = NilAllTs
-- replicateAllTs (Succ n) = ConsAllTs $ replicateAllTs n

-- deleteAllTs :: TElem ix t_ ts -> AllTs t ts -> AllTs t (Delete ix ts)
-- deleteAllTs THere (ConsAllTs ts) = ts
-- deleteAllTs (TThere loc) (ConsAllTs ts) = ConsAllTs $ deleteAllTs loc ts

-- prodAllTs :: AllTs t ts -> TProd f ts -> [f t]
-- prodAllTs NilAllTs MkNilProd = []
-- prodAllTs (ConsAllTs n) (MkCProd v vs) = v : prodAllTs n vs

-- invertElemAllTs :: AllTs t ts -> TElem ix t_ ts -> t :=: t_
-- invertElemAllTs (ConsAllTs _) THere = Refl
-- invertElemAllTs (ConsAllTs allTs) (TThere t) = invertElemAllTs allTs t


-- a type of applicative-polymorphic functions from type lists to type lists
data AnyAppNFun f asmpts results =
  MkAANFun {
    unAANFun :: forall b. Applicative b => TArrs (Compose f b) asmpts results
    }

composeAANFun :: (forall f. TProd f nts -> TProd f ts) ->
                 forall f. AnyAppNFun f ts res -> AnyAppNFun f nts res
composeAANFun i fs = MkAANFun $ unAANFun fs . i
 
deleteAANFun :: TElem ix t results -> AnyAppNFun f asmpts results ->
              AnyAppNFun f asmpts (Delete ix results)
deleteAANFun loc fs = MkAANFun $ arrsDelete loc (unAANFun fs)

applyAANFun ::
  Applicative b => TElem ix t ts -> AnyAppNFun f asmpts ts ->
  TProd (Compose f b) asmpts -> Compose f b t
applyAANFun loc fs args = arrsIndex loc (unAANFun fs) args
 


-- zipper view of a type list
data TSplit ix ts1 ts2 ts where
  NilTSplit :: TSplit Zero TNil ts2 ts2
  ShiftTSplit :: TSplit ix ts1 (t ::: ts2) ts ->
                 TSplit (Succ ix) (t ::: ts1) ts2 ts

-- GHC 7.0.4 wrongly complains that patterns are non-exhaustive..
unSplitProd :: ListU ts1 -> TSplit ix ts1 ts2 ts ->
               TProd f ts1 -> TProd f ts2 -> TProd f ts
unSplitProd TNil NilTSplit MkNilProd p2 = p2
unSplitProd (_t ::: ts1) (ShiftTSplit splt) (MkCProd v p1) p2 =
  unSplitProd ts1 splt p1 (MkCProd v p2)

-- "prove" that TSplit index is always a natural
indexTSplitIsNat :: TSplit ix ts1 ts2 ts -> NatU ix
indexTSplitIsNat NilTSplit = Zero
indexTSplitIsNat (ShiftTSplit splt) = Succ $ indexTSplitIsNat splt


-- a split primitive
-- note that for convenience, we allow the type argument of TElem to be anything;
-- we will derive that it has to be equal to t during pattern matching
-- split :: Applicative f => 
--          NatU n -> TElem ix t_ (TReplicate n t) -> TArr f (TReplicate n t) [f t]
-- split (Succ n) THere (MkCProd _v vs) = prodReplicate n vs
-- split (Succ n) (TThere loc) (MkCProd v vs) = v : split n loc vs



-- swap inside split
swapSplit :: forall ix ts1 ts2 ts ix2.
             TSplit ix ts1 ts2 ts -> NatU ix2 ->
             TSplit ix ts1 (Swap ix2 ts2) (Swap (ix :+: ix2) ts)
swapSplit NilTSplit _ix2 = NilTSplit
swapSplit (ShiftTSplit splt) ix2 =
  subst (congSwap (succPlus (indexTSplitIsNat splt) ix2) (Refl :: ts :=: ts)) $
  ShiftTSplit $ swapSplit splt (Succ ix2)

swapSplitZero :: forall ix ts1 t1 t2 ts2 ts.
                 TSplit ix ts1 (t1 ::: (t2 ::: ts2)) ts -> 
                 TSplit ix ts1 (t2 ::: (t1 ::: ts2)) (Swap ix ts)
swapSplitZero splt = 
  subst (congSwap (plusRightZero (indexTSplitIsNat splt)) (Refl :: ts :=: ts)) $
  swapSplit splt Zero



-- swapping in type lists: universe level functions
data Swappable ix ts where
  HereSwappable :: Swappable Zero (t1 ::: (t2 ::: ts))
  ThereSwappable :: Swappable ix ts -> Swappable (Succ ix) (t ::: ts)

swapMorphism1 :: Swappable ix ts -> TProd f ts -> TProd f (Swap ix ts)
swapMorphism1 HereSwappable (MkCProd v1 (MkCProd v2 vs)) = MkCProd v2 (MkCProd v1 vs)
swapMorphism1 (ThereSwappable swappable) (MkCProd v vs) = MkCProd v (swapMorphism1 swappable vs)

swapMorphism2 :: Swappable ix ts -> TProd f (Swap ix ts) -> TProd f ts 
swapMorphism2 HereSwappable (MkCProd v1 (MkCProd v2 vs)) = MkCProd v2 (MkCProd v1 vs)
swapMorphism2 (ThereSwappable swappable) (MkCProd v vs) = MkCProd v (swapMorphism2 swappable vs)

swappableIndexIsNat :: Swappable ix ts -> NatU ix
swappableIndexIsNat HereSwappable = Zero
swappableIndexIsNat (ThereSwappable swappable) = Succ $ swappableIndexIsNat swappable

splitToSwappable :: TSplit ix ts1 (t2 ::: (t ::: ts2)) nts ->
                    Swappable ix nts
splitToSwappable splt_ =
  coerce (cong2 (plusRightZero (indexTSplitIsNat splt_)) Refl) $
  go splt_ HereSwappable 
  where
    go :: TSplit ix ts1 ts2 ts -> Swappable ixs ts2 -> Swappable (ix :+: ixs) ts
    go NilTSplit sw = sw
    go (ShiftTSplit splt) sw = 
      coerce (cong2 (succPlus (indexTSplitIsNat splt) (swappableIndexIsNat sw)) Refl) $
      go splt (ThereSwappable sw)

moveToFront :: ListU ts -> TElem ixT t ts2 -> TSplit ix ts1 ts2 ts ->
               (forall nts . ListU nts ->
                 TSplit (Succ ix) (t ::: ts1) (Delete ixT ts2) nts ->
                 (forall f. TProd f nts -> TProd f ts) ->
                 (forall f. TProd f ts -> TProd f nts) -> b) -> b
moveToFront ts THere splt k = k ts (ShiftTSplit splt) id id
moveToFront ts (TThere (loc :: TElem ixT t ts2)) splt k =
  moveToFront ts loc (ShiftTSplit splt) $
  -- GHC 7.0.4 wrongly complains that patterns are non-exhaustive..
  \nts (ShiftTSplit (ShiftTSplit (nsplit :: TSplit ix ts1 (t2 ::: t ::: Delete ixT ts2) nts) )) permute1 permute2 ->
  let nnsplit :: TSplit (Succ ix) (t ::: ts1) (t2 ::: (Delete ixT ts2)) (Swap ix nts)
      nnsplit = ShiftTSplit (swapSplitZero nsplit)
  in k (listSwap (splitToSwappable nsplit) nts) nnsplit (permute1 . swapMorphism2 (splitToSwappable nsplit)) (swapMorphism1 (splitToSwappable nsplit) . permute2)


-- the main function
nafixG ::
  forall f b tsAll tsg tsfix ix . (ApplicativeFix f, Applicative b) =>
  ListU tsAll -> ListU tsg -> ListU tsfix -> TSplit ix tsg tsfix tsAll ->
  AnyAppNFun f tsAll tsfix ->                             -- pattern functors
  TProd (Compose f b) tsg ->                                          -- ts already fixed over
  TProd (Compose f b) tsfix
nafixG tsAll tsg tsfix theSplit
  fs asmpts =
    tabulate tsfix $ \t (tInTsFix :: TElem ixT t tsfix) ->
      fixCompose $ \(s :: Compose f (Compose b2 b) t) ->
        moveToFront tsAll tInTsFix theSplit $ \nts nsplit permute1 _permute2 ->
        let nasmpts :: TProd (Compose f (Compose b2 b)) (t ::: tsg)
            nasmpts = MkCProd s $ liftATProd liftComposed tsg asmpts
            fixedRest :: TProd (Compose f (Compose b2 b)) (Delete ixT tsfix)
            fixedRest = nafixG nts (t ::: tsg) (deleteList tInTsFix tsfix) nsplit (composeAANFun permute1 $ deleteAANFun tInTsFix fs) nasmpts
        in applyAANFun tInTsFix fs $
           permute1 $ 
           unSplitProd (t ::: tsg) nsplit nasmpts fixedRest 

-- multi fixpoint
type NFixable f ts = AnyAppNFun f ts ts

nafix :: ApplicativeFix f => ListU ts -> NFixable f ts -> TProd f ts 
nafix ts pf = liftATProd runIdentityCompose ts $ nafixG ts TNil ts NilTSplit pf MkNilProd

nafix2 :: ApplicativeFix f => ListU ts -> TProd (WrapTArrD f ts) ts -> TProd f ts 
nafix2 ts fs = nafix ts $ unWrapProd ts fs

-- curried TArr's...
type family TArrD (f :: * -> *) as t
type instance TArrD f TNil t = t
type instance TArrD f (a ::: as) t = f a -> TArrD f as t

data WrapTArrD f as t where 
  Wrap :: (forall b. Applicative b => Phantom1 b ->
           TArrD (Compose f b) as (Compose f b t)) -> WrapTArrD f as t

unWrap :: forall f b as t. Applicative b => Phantom1 b ->
          WrapTArrD f as t -> TArrD (Compose f b) as (Compose f b t)
unWrap pfb (Wrap f) = f pfb

fmapTArrD  :: ListU ts -> Phantom1 f -> (a -> b) -> TArrD f ts a -> TArrD f ts b
fmapTArrD TNil _pf f v = f v
fmapTArrD (_t ::: ts) pf f g = fmapTArrD ts pf f . g

mkCProdF :: Phantom1 f -> ListU ts -> f t -> TProd f ts -> TProd f (t ::: ts)
mkCProdF _pf _ts v vs = MkCProd v vs

mkProd :: ListU ts -> Phantom1 f -> TArrD f ts (TProd f ts)
mkProd TNil _pf = MkNilProd
mkProd (_t ::: ts) pf =
  \a -> fmapTArrD ts pf (mkCProdF pf ts a) $ mkProd ts pf

uncurryTArr :: ListU as -> TArrD f as t -> TArr f as t
uncurryTArr TNil f _args = f
uncurryTArr (_t ::: ts) f (MkCProd v vs) = uncurryTArr ts (f v) vs

unWrapProd :: forall ts f . ListU ts -> TProd (WrapTArrD f ts) ts -> NFixable f ts
unWrapProd ts fs = MkAANFun $ \(args :: TProd (Compose f b) ts) ->
  liftATProd (($args) . (uncurryTArr ts :: TArrD (Compose f b) ts (Compose f b t) -> TArr (Compose f b) ts (Compose f b t)) . unWrap (undefined :: Phantom1 b)) ts fs

nafix3 :: forall f ts . ApplicativeFix f => Phantom1 f -> ListU ts ->
          (TArrD (WrapTArrD f ts) ts (TProd f ts))
nafix3 _f ts = 
  let
    k :: TProd (WrapTArrD f ts) ts -> TProd f ts
    k pfs = nafix ts $ unWrapProd ts pfs
  in fmapTArrD ts (undefined :: Phantom1 (WrapTArrD f ts)) k
       (mkProd ts (undefined :: Phantom1 (WrapTArrD f ts)))

