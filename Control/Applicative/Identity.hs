module Control.Applicative.Identity where

import Control.Applicative

newtype Identity a = Identity {runIdentity :: a}

instance Functor Identity where
  fmap f v = Identity $ f $ runIdentity v

instance Applicative Identity where
  pure = Identity
  f <*> v = Identity $ runIdentity f $ runIdentity v
