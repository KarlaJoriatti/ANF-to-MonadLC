{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeOperators, DataKinds, RankNTypes #-} 
import Control.Eff
import Control.Eff.Extend
import Debug.Trace
import qualified Prelude as P

data Console x where
    Print :: x -> Console ()

print x = send (Print x)

data Exception x where
   Throw :: P.String -> Exception () 

throw x0 = send (Throw x0)

eapp :: P.Monad m => m (a -> m b) -> m a -> m b
eapp f x = do
   res <- f P.<*> x
   res


safedivision :: (Member Exception t1) => P.Int -> Eff t0 (P.Int -> Eff t1 P.Int )
safedivision a0 = 
  P.return P.$ \b0 -> do
   let bl2 _ = do 
           let bl3 _ = do 
                   _ <- ( P.return throw `eapp` P.return "\"can't divide by zero\"")
                   ( P.return bl4 `eapp` P.return ())
               bl4 _ = do 
                   P.return (a0  `P.div`  b0)
           var <- P.return (b0  P.==  0)
           if var
           then ( P.return bl3 `eapp` P.return ())
           else ( P.return bl4 `eapp` P.return ())
   ( P.return bl2 `eapp` P.return ())

