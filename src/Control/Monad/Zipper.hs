{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Control.Monad.Zipper where

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error.Class
import Control.Monad.Writer

newtype (t1 :> (t2 :: (* -> *) -> * -> *))  m a = Z { runZ :: t1 (t2 m) a }

leftL   = runZ
rightL  = Z

instance (MonadTrans t1, MonadTrans t2, Monad m) => Monad ((t1 :> t2) m) where
  return x  = returnZ x
  m >>= f   = m `bindZ` f

returnZ :: forall a t1 t2 m. (MonadTrans t1, MonadTrans t2, Monad m) => a -> (t1 :> t2) m a
returnZ x = case (mt :: Transformation t2 m) of
              MT -> case (mt :: Transformation t1 (t2 m)) of
                      MT -> Z $ return x

bindZ :: forall a b t1 t2 m. (MonadTrans t1, MonadTrans t2, Monad m)
      => (t1 :> t2) m a -> (a -> (t1 :> t2) m b) -> (t1 :> t2) m b
m `bindZ` f = case (mt :: Transformation t2 m) of
                MT -> case (mt :: Transformation t1 (t2 m)) of
                        MT -> Z $ runZ m >>= runZ . f

instance (MonadTrans t1, MonadTrans t2) => MonadTrans (t1 :> t2) where
  lift m  = liftZ m
  mt      = MT
  unlift  = unliftZ

liftZ :: forall a t1 t2 m. (MonadTrans t1, MonadTrans t2, Monad m) => m a -> (t1 :> t2) m a
liftZ m = case (mt :: Transformation t2 m) of
            MT -> Z $ lift $ lift $ m

unliftZ :: forall m n a t1 t2. (Monad m, Monad n, MonadTrans t1, MonadTrans t2)
        => (forall f. Functor f => (forall x. (t1 :> t2) m x -> m (f x)) -> n (f a)) -> (t1 :> t2) n a
unliftZ f = case (mt :: Transformation t2 m) of
              MT -> case (mt :: Transformation t2 n) of
                      MT -> Z $ unlift $ \ul1 -> unlift $ \ul2 -> liftM runFComp $ f $ \m -> liftM FComp $ ul2 $ ul1 $ runZ $ m

newtype FComp f1 f2 a = FComp { runFComp :: f1 (f2 a) }
instance (Functor f1, Functor f2) => Functor (FComp f1 f2) where
  fmap f = FComp . fmap (fmap f) . runFComp


{-
tmixmapZ :: forall c t1 t2 m n. (MonadTrans t1, MonadTrans t2, Monad m, Monad n) =>
              (forall a. m a -> n a) -> (forall b. n b -> m b) -> Z t1 t2 m c -> Z t1 t2 n c
tmixmapZ f g m = case (mt :: Transformation t2 m) of
                   MT -> case (mt :: Transformation t2 n) of
                           MT -> Z $ tmixmap (tmixmap f g) (tmixmap g f) $ runZ m
-}

-- #############################################################################

instance (MonadTrans t1, MonadTrans t2, Monad m, MonadState s (t2 m))
      => MonadState s ((t1 :> t2) m) where
  get   = Z $ lift $ get
  put s = Z $ lift $ put s


instance (MonadTrans t1, MonadTrans t2, Monad m, MonadError e (t2 m))
      => MonadError e ((t1 :> t2) m) where
  throwError e   = Z $ lift $ throwError e
  catchError m h = Z $ unlift (\ul -> ul (runZ m) `catchError` (ul . runZ . h))

instance (MonadTrans t1, MonadTrans t2, Monad m, MonadReader e (t2 m))
     => MonadReader e ((t1 :> t2) m) where
  ask        = Z $ lift $ ask
  local f m  = Z $ unlift (\ul -> local f (ul $ runZ m))


instance (MonadTrans t1, MonadTrans t2, Monad m, MonadWriter w (t2 m))
     => MonadWriter w ((t1 :> t2) m) where
  tell c    = Z $ lift $ tell c
  -- listen = ??
  -- pass   = ??
