{-# LANGUAGE RankNTypes #-}
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
import qualified Data.Kind as Kind
import qualified Control.Monad.Reader as Monad.Reader
import Data.Functor.Identity(Identity)
import GHC.Generics (Generic)


data NetworkState = Active | Inactive 
  deriving (Read,Eq,Show,Generic)

data Status = Connected | Unconnected
  deriving (Read,Eq,Show,Generic)

data Messages a = None | Ping | Pong | Change a


data TestNetworkProfile = N1 | N2 
  deriving (Read,Eq,Show,Generic)



data State p = State {
  currentNetworkProfile :: p, 
  previousNetworkProfile :: p 
}

type SystemState m = State (NetworkProfile m)

-- | Our time type, usually UTCTime in prod and Int in testing
-- We are going to assume given states in our tla model of:
-- NetworkState, NetworkProfile, Status, Messages
-- Are not available to the system in a pure way by default
-- therefore effect interfaces must be created to gather these states
-- time is another value that must be gathered by side effect.

class PingSyncSharedTypes (m:: (Kind.Type -> Kind.Type )) where
  type Tick m  :: Kind.Type 
  type NetworkProfile m 
  

class PingSyncSharedTypes m => HasTimer m  where
  getTick :: m  (Tick m)  

-- | in the live system these would be the effects gathered by network
-- actions 
class PingSyncSharedTypes m =>   PingSyncNetworkEff m where
  getNetworkState :: m NetworkState
  setNetworkState :: NetworkState -> m NetworkState
  getNetworkProfile :: m (NetworkProfile m)  
  setNetworkProfile :: (NetworkProfile m) -> m (NetworkProfile m)
  getStatus :: m Status 
  getMessage :: m (Messages (NetworkProfile m))
    
-- | In the live system these would be the effects gathered by persistence
class PingSyncSharedTypes m => PingSyncStorageEff m where
  getSystemState :: m (SystemState m)  
  modifySystemState :: ((SystemState m) -> (SystemState m)) -> m (SystemState m)
  putSystemState :: (SystemState m) -> m ()
   
-----------------------------------------------------
-- Envionrment and Monad Reader
--------------------------------------------------
type PingSyncM = Monad.Reader.ReaderT SystemEnv IO
type PingSyncTestM = Monad.Reader.ReaderT SystemEnv Identity

data SystemEnv = SystemEnv
  { env :: ()}




newtype Time = Time { unTime :: Int}




runActionsOnMessageChange
  :: Monad m =>
     PingSyncNetworkEff m =>
     PingSyncStorageEff m =>
     (NetworkProfile m -> m a) -> m ()
runActionsOnMessageChange action = do
  msgs <- getMessage 
  case msgs of 
    Change prof -> action prof >> return ()
    _ -> return ()

runSystem :: forall m . Monad m => 
             PingSyncNetworkEff m =>
             PingSyncStorageEff m =>
             m ()   
runSystem = do
  runActionsOnMessageChange deactivateSystem


deactivateSystem
  :: forall m .
     PingSyncStorageEff m =>
     PingSyncNetworkEff m =>
     Monad m => 
     NetworkProfile m -> m (State (NetworkProfile m))
deactivateSystem prof = do
  _ <- setNetworkState Inactive 
  activeProf <- setNetworkProfile prof
  modifySystemState (\p -> let lastProfile = currentNetworkProfile p
                           in  p {previousNetworkProfile = lastProfile,
                                  currentNetworkProfile = activeProf
                                                                    })  
  


runSystemIO :: IO () 
runSystemIO = putStrLn "System Started"
  

  
