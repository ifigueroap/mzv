{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module Control.Monad.Mask where

import Control.Monad.Identity
import Control.Monad.Zipper
import Control.Monad.State.Lazy
import Control.Monad.Error
import Control.Monad.Views (MonadMorphism (..), View (..), (:><:) (..), i, o, vcomp)


-- ========================= Nominal Masks =========================

newtype Tagged tag m a = Tag { unTag :: m a }

instance MonadTrans (Tagged tag) where
  lift       = Tag
  mt         = MT
  unlift   k = Tag $ k (\tm -> unTag tm >>= return . Identity) >>= return . runIdentity

instance Monad m => Monad (Tagged tag m) where
  return   = Tag . return
  m >>= f  = Tag $ unTag m >>= unTag . f

instance MonadState s m => MonadState s (Tagged t m) where
  get = lift get
  put = lift . put

-- Standard Tagged Transformers

type TStateT tag s m = Tagged tag (StateT s m)

runTStateT :: Monad m => s -> TStateT tag s m a -> m (a,s)
runTStateT s m = runStateT (unTag m) s

evalTStateT :: Monad m => s -> TStateT tag s m a -> m a
evalTStateT s m = evalStateT (unTag m) s

type TErrorT tag error m = Tagged tag (ErrorT error m)

runTErrorT :: Monad m => TErrorT tag e m a -> m (Either e a)
runTErrorT m = runErrorT (unTag m)

class (Monad m, Monad n) => TWith tag n m where
   structure :: View g => tag -> (n `g` m)

use     :: TWith tag n m => n a -> tag -> m a
c `use` name     = bifrom (structure name) c

expose  :: TWith tag n m => m a -> tag -> n a
c `expose` name  = bito (structure name) c

  -- [1] tag at the top
instance (Monad m, m ~ n) => TWith tag n (Tagged tag m) where
   structure _  = t -- idv

  -- auxiliary clause, to resolve overlap between [1] and [3]
instance (Monad m, m ~ t n, MonadTrans t) => TWith tag m (Tagged tag (t n)) where
   structure _  = t

  -- [2] tag in focus
instance (Monad m, Monad n, MonadTrans t, m ~ t n) => TWith tag m ((t :> Tagged tag) n) where
   structure _  = case (mt :: Transformation t (Tagged tag n)) of
                    MT -> inverse_o `hcomp` hmap t

  -- auxiliary clause, to resolve overlap between [2] and [3]
instance (Monad (t' n), Monad m, Monad n, MonadTrans t, m ~ (((t :> Tagged tag) :> t') n), MonadTrans t') => TWith tag m ((t :> Tagged tag) (t' n)) where
   structure _  = case (mt :: Transformation t' n) of
                   MT -> o

  -- [3] shift focus down
instance (Monad (t0 (t1 n)), Monad m, Monad n, TWith tag m ((t0 :> t1) n), MonadTrans t0, MonadTrans t1) => TWith tag m (t0 (t1 n)) where
   structure tag  =  case (mt :: Transformation t1 n) of
                       MT -> case (mt :: Transformation t0 (t1 n)) of
                               MT -> o `hcomp` structure tag

t :: View g => m `g` Tagged tag m
t = view Tag unTag

unt :: View g => Tagged tag m `g` m
unt = view unTag Tag

inverse_o  = view rightL leftL

data Log1 = Log1
data Log2 = Log2

ifpos1 :: MonadState Int m => m () -> m ()
ifpos1 c = do  x <- get
               if x > 0 then c else return ()

-- x98 = runIdentity $ runTStateT Counter2 5 $ runTStateT Counter1 0 $ c
-- x99 = runIdentity $ runTStateT Counter1 0 $ runTStateT Counter2 5 $ c

luse     :: LWith taglist n m => n a -> taglist -> m a
c `luse` namelist     = bifrom (lstructure namelist) c

data e :&: l = e :&: l

data HTrue  = HTrue
data HFalse = HFalse

class HMember e l b where
  hmember :: e -> l -> b

instance b ~ HTrue => HMember e e b where
  hmember _ _ = HTrue
instance b ~ HFalse => HMember e f b where
  hmember _ _ = HFalse
instance b ~ HTrue => HMember e (e :&: l) b where
  hmember _ _ = HTrue
instance HMember e l b => HMember e (f :&: l) b where
  hmember e (_ :&: l) = hmember e l

class LWith list (n :: * -> *) (m :: * -> *) where
  lstructure :: View g => list -> (n `g` m)

class LWith1 list b (n :: * -> *) (m :: * -> *) where
  lstructure1 :: View g => list -> b -> (n `g` m)

class LWith2 list b (n :: * -> *) (m :: * -> *) where
  lstructure2 :: View g => list -> b -> (n `g` m)

instance (HMember t l b, LWith1 l b n (Tagged t m), Monad m, Monad n) => LWith l n (Tagged t m) where
  lstructure list = lstructure1 list (hmember e list :: b)
    where e = undefined :: t

instance (HMember t l b, LWith2 l b n ((t0 :> Tagged t) m), Monad m, Monad n) => LWith l n ((t0 :> Tagged t) m) where
  lstructure list = lstructure2 list (hmember e list :: b)
    where e = undefined :: t

instance (m ~ n, Monad m, Monad n) => LWith l n m where
  lstructure list = idv

instance (Monad m, n ~ t n', Monad n', LWith list n' m, MonadTrans t) => LWith1 list HTrue n (Tagged e (t m)) where
  lstructure1 list _ = f list
    where f :: forall list m n n' t g e.
               (Monad m, n ~ t n', Monad n', LWith list n' m, MonadTrans t, View g) =>
               list -> n `g` (Tagged e (t m))
          f list =     case (mt :: Transformation t m) of
                         MT -> case (mt :: Transformation t n') of
                                 MT -> t `hcomp` (hmap (lstructure list :: n' `g` m))

instance (LWith list n ((:>) t t' m), Monad n, Monad m, MonadTrans t, MonadTrans t') => LWith1 list HFalse n (Tagged e (t (t' m))) where
  lstructure1 list _ = case (mt :: Transformation t' m) of
                        MT -> case (mt :: Transformation t (t' m)) of
                                MT -> t `hcomp` o `hcomp` lstructure list

instance (Monad m, n ~ (t0 :> t) n', Monad n', LWith list n' m, MonadTrans t, MonadTrans t0) => LWith2 list HTrue n ((t0 :> Tagged e) (t m)) where
  lstructure2 list _ = f list
    where f :: forall list m n t0 t n' e g.
               (Monad m, n ~ (t0 :> t) n', Monad n', LWith list n' m, MonadTrans t, MonadTrans t0, View g) =>
               list -> n `g` ((t0 :> Tagged e) (t m))
          f list =     case (mt :: Transformation t m) of
                         MT -> case (mt :: Transformation t0 (t m)) of
                                 MT -> case (mt :: Transformation t0 (Tagged e (t m))) of
                                         MT -> inverse_o `hcomp` hmap t `hcomp` o `hcomp` hmap (lstructure list :: n' `g` m)

instance (Monad m, Monad n, LWith list n ((t0 :> t1 :> t2) m), MonadTrans t2, MonadTrans t1, MonadTrans t0) => LWith2 list HFalse n ((t0 :> Tagged e) (t1 (t2 m))) where
  lstructure2 list _ = case (mt :: Transformation t2 m) of
                         MT -> case (mt :: Transformation t1 (t2 m)) of
                                 MT -> case (mt :: Transformation t0 (t1 (t2 m))) of
                                         MT -> case (mt :: Transformation t0 (Tagged e (t1 (t2 m)))) of
                                                 MT -> inverse_o `hcomp` hmap t `hcomp` o `hcomp` o `hcomp` (lstructure list)

getv v  = from v $ get
putv v  = from v . put
