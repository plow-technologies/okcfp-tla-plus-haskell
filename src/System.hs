{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}


-- |
-- Description : This Module is designed to be a reference implmentation 
-- For how one might interact between a tla model... in this case
-- ../models/PingSync.tla
-- From the model:
--
--  This is an algorithm to change network 
-- A server receives a request to change network settings but
-- then it needs to have a timeout and revert to old settings
-- if the new settings can't get a ping.


module System where

import qualified Control.Monad.Reader 

import GHC.Generics (Generic)


data NetworkState = Active | Inactive 
  deriving (Read,Eq,Show,Generic)

data NetworkProfile = N1 | N2 
  deriving (Read,Eq,Show,Generic)

data Status = Connected | Unconnected
  deriving (Read,Eq,Show,Generic)

data Messages = None | Ping | Pong | Change 


newtype Time = Time { unTime :: Int}


-- | Our time type, usually UTCTime in prod and Int in testing
class HasTick m where 
  type Tick m 
  getTick :: m 

class PingSyncInterface m where
 

runSystem :: IO () 
runSystem = putStrLn "System Started"
  

  
