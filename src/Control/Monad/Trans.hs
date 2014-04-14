-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans
-- Copyright   :  (c) Andy Gill 2001,
--                (c) Oregon Graduate Institute of Science and Technology, 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  portable
--
-- The MonadTrans class.
--
--      Inspired by the paper
--      /Functional Programming with Overloading and
--          Higher-Order Polymorphism/,
--        Mark P Jones (<http://web.cecs.pdx.edu/~mpj/>)
--          Advanced School of Functional Programming, 1995.
-----------------------------------------------------------------------------
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Control.Monad.Trans (
    MonadTrans(..),
    MonadIO(..),
    Transformation(..),
    tmap
  ) where

import System.IO

-- ---------------------------------------------------------------------------
-- MonadTrans class
--
-- Monad to facilitate stackable Monads.
-- Provides a way of digging into an outer
-- monad, giving access to (lifting) the inner monad.

data Transformation (t :: ((* -> *) -> * -> *)) (m :: * -> *)
  where MT :: Monad (t m) => Transformation t m

class MonadTrans t where
    lift     :: Monad m => m a -> t m a
    mt       :: Monad m => Transformation t m
    unlift   :: (Monad m, Monad n) => (forall f. Functor f => (forall x. t m x -> m (f x)) -> n (f a)) -> t n a 
    {-
    tmixmap  :: (Monad m, Monad n) =>
          (forall a. m a -> n a) -> (forall b. n b -> m b) -> t m c -> t n c
    -}
    tmixmap  :: (Monad m, Monad n) => (forall a. m a -> n a) -> t m c -> t n c
    tmixmap f m = unlift (\ul -> f $ ul m)

tmap  :: (MonadTrans t, Monad m, Monad n) => (forall a. m a -> n a) -> t m c -> t n c
tmap = tmixmap
      

class (Monad m) => MonadIO m where
    liftIO :: IO a -> m a

instance MonadIO IO where
    liftIO = id
