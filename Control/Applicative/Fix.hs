{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Applicative.Fix (
    module Control.Applicative
  , module Control.Applicative.Compose
  , Fixable
  , FixableNC
  , ApplicativeFix(..)
  , AlternativeFix(..)
  , liftComposed
  , fixCompose
  , fixToAfix
  , afixInf  
  , afixKill
  , BLInt(..)
  , manyAppFix, someAppFix
  ) where

import Control.Applicative hiding (some, many)
import Control.Applicative.Compose

type Fixable p a = forall p2. Applicative p2 => Compose p p2 a -> Compose p p2 a
type FixableNC p a = forall p2. Applicative p2 => p (p2 a) -> p (p2 a)

-- newtype Compose p1 p2 a = Compose { runCompose :: p1 (p2 a) }
class Applicative p => ApplicativeFix p where
--  type ApplicativeFixCtx p a :: Constraint
--  type ApplicativeFixCtx p a = ()
  --afix :: (forall b. Applicative b => Compose p b a -> Compose p b a) -> p a
  afix :: --ApplicativeFixCtx p a =>
          Fixable p a -> p a
  afix f = afixNC (runCompose . f . Compose)
  --afixNC :: (forall b. Applicative b => p (b a) -> p (b a)) -> p a
  afixNC :: -- ApplicativeFixCtx p a =>
            FixableNC p a -> p a
  afixNC f = afix (Compose . f . runCompose)

class Alternative p => AlternativeFix p where
  some, many :: p a -> p [a]

manyAppFix, someAppFix :: (Alternative p, ApplicativeFix p) => p a -> p [a]
someAppFix f = afix $ \ fs -> (:) <$> liftInside f <*> (pure [] <|> fs)
manyAppFix f = afix $ \ fs -> (:) <$> liftInside f <*> fs <|> pure []

liftComposed :: (Applicative h, Functor f, Functor g) => Compose f g v -> Compose f (Compose h g) v
liftComposed f = Compose $ (Compose <$>) $ pure <$> runCompose f

fixCompose :: (ApplicativeFix f, Applicative b
              -- , ApplicativeFixCtx f (b a)
              ) =>
              (forall b2. Applicative b2 =>
               Compose f (Compose b2 b) a -> Compose f (Compose b2 b) a) ->
              Compose f b a
fixCompose pf = Compose $ afixNC $ \s ->
  (runCompose <$>) $ runCompose $ pf (Compose $ Compose <$> s)

fix :: (t -> t) -> t
fix f = let s = fix f in f s

fixToAfix :: Applicative p => ((p a -> p a) -> p a) -> Fixable p a -> p a
fixToAfix fx f = fx $ runIdentityCompose . f . liftInside

afixInf :: Applicative p => Fixable p a -> p a
afixInf = fixToAfix fix

--afixKill :: (Alternative p) => (forall b. Applicative b => Compose p b a -> Compose p b a) ->
--            p a
afixKill :: (Alternative p) => Fixable p a -> p a
afixKill f = runIdentityCompose $ f empty

instance ApplicativeFix Identity where
  afix = afixInf

instance ApplicativeFix [] where
  afix = afixInf

instance ApplicativeFix Maybe where
  afix = afixInf

instance ApplicativeFix b => ApplicativeFix (Compose ((->) a) b) where
  --type ApplicativeFixCtx (Compose ((->) a) b) v = ApplicativeFixCtx b v
  afixNC (f :: forall b2. Applicative b2 => Compose ((->) a) b (b2 v) -> Compose ((->) a) b (b2 v)) = 
    Compose $ \(a :: a) -> afixNC $ \ (self :: b (b2 v)) ->
      runCompose (f (liftOutside self)) a

newtype BLInt p a = MkBLI { breakLoops :: p a } deriving (Functor, Applicative, Alternative)

instance Alternative p => ApplicativeFix (BLInt p) where
  afix f = afixKill f

instance Alternative p => AlternativeFix (BLInt p) where
  some = ((:[]) <$>)
  many = const $ pure []

