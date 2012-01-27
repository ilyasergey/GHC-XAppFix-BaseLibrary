{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Applicative.Compose where

import Control.Applicative

newtype Compose p1 p2 a = Compose { runCompose :: p1 (p2 a) }

instance (Functor p1, Functor p2) => Functor (Compose p1 p2) where
  fmap f p = Compose (fmap (fmap f) $ runCompose p)

instance (Applicative p1, Applicative p2) => Applicative (Compose p1 p2) where
  pure v = Compose $ pure $ pure v
  va <*> vb = Compose $ liftA2 (<*>) (runCompose va) (runCompose vb)

instance (Alternative p1, Applicative p2) => Alternative (Compose p1 p2) where
  empty = Compose empty
  va <|> vb = Compose $ runCompose va <|> runCompose vb

type AppFun p b a = forall p2. Applicative p2 => Compose p p2 b -> Compose p p2 a
type AppFunNC p b a = forall p2. Applicative p2 => p (p2 b) -> p (p2 a)

assocCompose1 :: Functor p1 => Compose (Compose p1 p2) p3 v -> Compose p1 (Compose p2 p3) v 
assocCompose1 w = Compose $ Compose <$> runCompose (runCompose w)

assocCompose2 :: Functor p1 => Compose p1 (Compose p2 p3) v -> Compose (Compose p1 p2) p3 v
assocCompose2 w = Compose $ Compose $ runCompose <$> runCompose w


openApp :: forall p c b a.
           Applicative p => (forall p2. Applicative p2 => Compose p p2 b -> Compose p p2 a) ->
           p (c -> b) -> p (c -> a)
openApp f v = runCompose $ f $ Compose v

coapp :: Applicative p => AppFun p b a -> p (b -> a)
coapp f = openApp f (pure id)

openAppNC :: Applicative p => AppFunNC p b a -> p (c -> b) -> p (c -> a)
openAppNC f v = f v

coappNC :: Applicative p => AppFunNC p b a -> p (b -> a)
coappNC f = openAppNC f (pure id)

coappG :: forall p1 p3 b a. (Applicative p1, Applicative p3) =>
          AppFun p1 b a -> p1 (p3 b -> p3 a)
coappG f = runCompose <$> (runCompose $ f $ Compose $ pure $ Compose id)

coappG_ :: forall p1 p3 b a. (Applicative p1, Applicative p3) =>
          AppFun p1 b a -> Compose p1 p3 (b -> a)
coappG_ (f :: forall p2. Applicative p2 => Compose p1 p2 b -> Compose p1 p2 a) =
  -- p2 = Compose p3 ((->) b)
  Compose $ (runCompose <$>) $ runCompose $ f $ liftOutside $ liftOutside id


liftInside :: (Applicative p, Applicative b) => p a -> Compose p b a
liftInside = Compose . (pure <$>)

liftOutside :: (Applicative p, Applicative b) => b a -> Compose p b a
liftOutside = Compose . pure 

runIdentityCompose :: Functor p => Compose p Identity a -> p a
runIdentityCompose = (runIdentity <$>) . runCompose

withOuter :: (forall v. p v -> q v) -> Compose p b a -> Compose q b a
withOuter f = Compose . f . runCompose

withInner :: Functor p => (forall v. b v -> c v) -> Compose p b a -> Compose p c a
withInner f = Compose . (f <$>) . runCompose
