{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- Needed for the same reasons as in Reader, State etc

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.List
-- Copyright   :  (c) Andy Gill 2001,
--                (c) Oregon Graduate Institute of Science and Technology, 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable (multi-parameter type classes)
--
-- The List monad.
--
-----------------------------------------------------------------------------

module Control.Monad.List (
    ListT(..),
    mapListT,
    module Control.Monad,
    module Control.Monad.Trans,
  ) where

import Control.Monad
import Control.Monad.Cont.Class
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Trans

-- ---------------------------------------------------------------------------
-- Our parameterizable list monad, with an inner monad

newtype ListT m a = ListT { runListT :: m [a] }

mapListT :: (m [a] -> n [b]) -> ListT m a -> ListT n b
mapListT f m = ListT $ f (runListT m)

instance (Monad m) => Functor (ListT m) where
    fmap f m = ListT $ do
        a <- runListT m
        return (map f a)

instance (Monad m) => Monad (ListT m) where
    return a = ListT $ return [a]
    m >>= k  = ListT $ do
        a <- runListT m
        b <- mapM (runListT . k) a
        return (concat b)
    fail _ = ListT $ return []

instance (Monad m) => MonadPlus (ListT m) where
    mzero       = ListT $ return []
    m `mplus` n = ListT $ do
        a <- runListT m
        b <- runListT n
        return (a ++ b)

-- ---------------------------------------------------------------------------
-- Instances for other mtl transformers

instance MonadTrans ListT where
    lift m = ListT $ do
        a <- m
        return [a]

instance (MonadIO m) => MonadIO (ListT m) where
    liftIO = lift . liftIO

instance (MonadCont m) => MonadCont (ListT m) where
    callCC f = ListT $
        callCC $ \c ->
        runListT (f (\a -> ListT $ c [a]))

instance (MonadError e m) => MonadError e (ListT m) where
    throwError       = lift . throwError
    m `catchError` h = ListT $ runListT m
        `catchError` \e -> runListT (h e)

instance (MonadReader s m) => MonadReader s (ListT m) where
    ask       = lift ask
    local f m = ListT $ local f (runListT m)

instance (MonadState s m) => MonadState s (ListT m) where
    get = lift get
    put = lift . put

