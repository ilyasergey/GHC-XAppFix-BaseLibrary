{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Applicative.Compose where

import Control.Applicative
import Control.Applicative.Identity

newtype Compose p1 p2 a = Comp { comp :: p1 (p2 a) }

instance (Functor p1, Functor p2) => Functor (Compose p1 p2) where
  fmap f p = Comp (fmap (fmap f) $ comp p)

instance (Applicative p1, Applicative p2) => Applicative (Compose p1 p2) where
  pure v = Comp $ pure $ pure v
  va <*> vb = Comp $ liftA2 (<*>) (comp va) (comp vb)

instance (Alternative p1, Applicative p2) => Alternative (Compose p1 p2) where
  empty = Comp empty
  va <|> vb = Comp $ comp va <|> comp vb

type AppFun p b a = forall p2. Applicative p2 => Compose p p2 b -> Compose p p2 a
type AppFunNC p b a = forall p2. Applicative p2 => p (p2 b) -> p (p2 a)

assocCompose1 :: Functor p1 => Compose (Compose p1 p2) p3 v -> Compose p1 (Compose p2 p3) v 
assocCompose1 w = Comp $ Comp <$> comp (comp w)

assocCompose2 :: Functor p1 => Compose p1 (Compose p2 p3) v -> Compose (Compose p1 p2) p3 v
assocCompose2 w = Comp $ Comp $ comp <$> comp w


openApp :: forall p c b a.
           Applicative p => (forall p2. Applicative p2 => Compose p p2 b -> Compose p p2 a) ->
           p (c -> b) -> p (c -> a)
openApp f v = comp $ f $ Comp v

coapp :: Applicative p => AppFun p b a -> p (b -> a)
coapp f = openApp f (pure id)

openAppNC :: Applicative p => AppFunNC p b a -> p (c -> b) -> p (c -> a)
openAppNC f v = f v

coappNC :: Applicative p => AppFunNC p b a -> p (b -> a)
coappNC f = openAppNC f (pure id)

coappG :: forall p1 p3 b a. (Applicative p1, Applicative p3) =>
          AppFun p1 b a -> p1 (p3 b -> p3 a)
coappG f = comp <$> (comp $ f $ Comp $ pure $ Comp id)

coappG_ :: forall p1 p3 b a. (Applicative p1, Applicative p3) =>
          AppFun p1 b a -> Compose p1 p3 (b -> a)
coappG_ (f :: forall p2. Applicative p2 => Compose p1 p2 b -> Compose p1 p2 a) =
  -- p2 = Compose p3 ((->) b)
  Comp $ (comp <$>) $ comp $ f $ liftInner $ liftInner id


liftOuter :: (Applicative p, Applicative b) => p a -> Compose p b a
liftOuter = Comp . (pure <$>)

liftInner :: (Applicative p) => b a -> Compose p b a
liftInner = Comp . pure 

runIdComp :: Functor p => Compose p Identity a -> p a
runIdComp = (runIdentity <$>) . comp

wrapIdComp :: Applicative p => (forall b . Applicative b => Compose p b a -> Compose p b a) -> p a -> p a
wrapIdComp f s = runIdComp $ f $ liftOuter s

withOuter :: (forall v. p v -> q v) -> Compose p b a -> Compose q b a
withOuter f = Comp . f . comp

withInner :: Functor p => (forall v. b v -> c v) -> Compose p b a -> Compose p c a
withInner f = Comp . (f <$>) . comp
