{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.Monad.Views where

import Control.Monad.Zipper
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer

class MonadMorphism g where
  idv        ::  (Monad m) =>  m `g` m
  hcomp      ::  (Monad l, Monad m, Monad n) 
             =>  (m `g` n) -> (l `g` m) -> (l `g` n)
  hmap       ::  (Monad m, Monad n, MonadTrans t) 
             =>  (m `g` n) -> (t m `g` t n)
  from       ::  (Monad m, Monad n) =>  (n `g` m) -> n a -> m a

htmap :: (Monad (t1 n), Monad (t2 n), Monad m, Monad n, Monad (t1 m),
          MonadTrans t1, MonadMorphism g) =>
         (forall m . Monad m => t1 m `g` t2 m) -> (m `g` n) -> t1 m `g` t2 n
htmap t f = t `hcomp` hmap f

newtype n :-> m = Uni (forall a. n a -> m a)

instance MonadMorphism (:->) where
  idv            = Uni id
  v2 `hcomp` v1  = Uni $ from v2 .from v1
  hmap v         = Uni $ tmap (from v)
  from (Uni v)   = v

liftv :: (MonadTrans t, Monad m) => m :-> t m
liftv = Uni lift

r1 :: (MonadTrans t, Monad m, MonadState s (t m)) => ReaderT s m :-> t m
r1 = Uni $ \n ->  do  s <- get 
                      lift $ runReaderT n s

ra = Uni (\n ->  do  s <- get
                     lift $ runReaderT n s )

data n :><: m = Bi  { bifrom  :: forall a. n a -> m a
                    , bito    :: forall a. m a -> n a}

instance MonadMorphism (:><:) where
  idv            = Bi  { bifrom  = id
                       , bito    = id }
  v2 `hcomp` v1  = Bi  { bifrom  = bifrom v2 . bifrom v1
                       , bito    = bito v1 . bito v2     }
  hmap v         = Bi  { bifrom  = tmap (from v)
                       , bito    = tmap (to v)  }
  from v         = bifrom v

to :: (Monad n, Monad m) => n :><: m -> m a -> n a
to = bito

inverse ::  (Monad n, Monad m) =>  n :><: m -> m :><: n
inverse (Bi from to) = Bi to from

class MonadMorphism g => View g where
  view :: (forall a. n a -> m a) -> (forall a. m a -> n a) -> n `g` m

instance View (:->)  where view f fm1 = Uni f

instance View (:><:) where view f fm1 = Bi f fm1

stateIso  :: (Monad m, View g) 
          => (s2 -> s1) -> (s1 -> s2) -> StateT s2 m `g` StateT s1 m
stateIso f fm1 = view (iso f fm1) (iso fm1 f) where
  iso g h m = StateT $ \s2 -> do  (a, s1) <- runStateT m (h s2)
                                  return (a, g s1)

newtype MonadStateReaderT s m a = MonadStateReaderT { runMonadStateReaderT :: m a }

instance MonadState s m => MonadReader s (MonadStateReaderT s m) where
  ask   = MonadStateReaderT get
  local f m = MonadStateReaderT $ 
    do s <- get
       put (f s)
       r <- runMonadStateReaderT m
       put s
       return r

instance MonadWriter w m => MonadWriter w (MonadStateReaderT s m) where
    tell     = lift . tell
    listen m = MonadStateReaderT $ do (ma, w) <- listen (runMonadStateReaderT m)
                                      return (ma, w)
    pass m   = MonadStateReaderT $ pass $ do
                                   (ma, w) <- runMonadStateReaderT m
                                   return (ma, w)

instance MonadTrans (MonadStateReaderT s)
 where
  lift      = MonadStateReaderT
  mt        = MT
  unlift f  = MonadStateReaderT $ liftM runIdentity $ f (\tmx -> liftM Identity $ runMonadStateReaderT tmx)

r2 :: (MonadState s m, View g) => MonadStateReaderT s m `g` m
r2 = view runMonadStateReaderT MonadStateReaderT

instance Monad m => Monad (MonadStateReaderT s m) where
  return   = MonadStateReaderT . return
  x >>= f  = MonadStateReaderT $ runMonadStateReaderT x >>= runMonadStateReaderT . f

-- ========================= Structural Masks =========================

infixl 5 `vcomp`

i  ::  (Monad m, View g) =>  m `g` m
i = idv

o  ::  (MonadTrans t1, MonadTrans t2, Monad m, View g) 
   =>  (t1 :> t2) m `g` t1 (t2 m) 
o  = view leftL rightL 

v1 `vcomp` v2  = v1 `hcomp` hmap v2
