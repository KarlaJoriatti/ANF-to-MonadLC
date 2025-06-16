{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeOperators, DataKinds, RankNTypes #-} 
import Control.Eff
import Control.Eff.Extend
import Debug.Trace
import qualified Prelude as P

data Console x where
    Print :: x -> Console ()

print x = send (Print x)

eapp :: P.Monad m => m (a -> m b) -> m a -> m b
eapp f x = do
   res <- f P.<*> x
   res


fatorial :: P.Int -> Eff t0 P.Int 
fatorial n0 = do
  let bl2 _ = do 
          let bl3 _ = do 
                  ( ( P.* )  P.<$> P.return n0 P.<*> ( P.return fatorial `eapp` P.return (n0  P.-  1)))
              bl4 _ = do 
                  P.return 1
          f0 <- P.return (n0  P.>  1)
          if f0
          then ( P.return bl3 `eapp` P.return ())
          else ( P.return bl4 `eapp` P.return ())
  ( P.return bl2 `eapp` P.return ())

