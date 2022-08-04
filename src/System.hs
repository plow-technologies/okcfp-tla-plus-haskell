{-# LANGUAGE FlexibleContexts #-}
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


data NetworkState = Active | Inactive | Timeout
  deriving (Read,Eq,Show,Generic)

data Status = Connected | Unconnected 
  deriving (Read,Eq,Show,Generic)

data Messages a = None | Ping | Pong | Change a

data SystemError = SystemError

data TestNetworkProfile = N1 | N2 
  deriving (Read,Eq,Show,Generic)



data State p t = State {
  currentNetworkProfile :: p, 
  previousNetworkProfile :: p,
  timeout :: t 
}

type SystemState m = State (NetworkProfile m) (Tick m)

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
  getTick :: m  (Either SystemError (Tick m))  

-- | in the live system these would be the effects gathered by network
-- actions 
class PingSyncSharedTypes m =>   PingSyncNetworkEff m where
  getNetworkState :: m (Either SystemError NetworkState)
  setNetworkState :: NetworkState -> m (Either SystemError NetworkState)
  getNetworkProfile :: m (Either SystemError (NetworkProfile m))  
  setNetworkProfile :: (NetworkProfile m) -> m (Either SystemError (NetworkProfile m))
  getStatus :: m Status 
  getMessage :: m (Either SystemError (Messages (NetworkProfile m)))
    
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
  :: (Monad m, PingSyncNetworkEff m) =>
     (PingSyncStorageEff m) => 
     (NetworkProfile m -> m a) -> m ()
runActionsOnMessageChange action = do
  msgs <- getMessage 
  case msgs of 
    (Right (Change prof)) -> action prof >> return ()
    _ -> return ()

runSystem ::
  (Monad m, PingSyncNetworkEff m) =>
     (PingSyncStorageEff m) =>
     m ()
runSystem =  do
   runActionsOnMessageChange deactivateSystem


deactivateSystem
  :: (Monad m, PingSyncNetworkEff m, PingSyncStorageEff m) =>
     NetworkProfile m
     -> m (Either SystemError (SystemState m))
deactivateSystem prof = do
  _ <- setNetworkState Inactive 
  eitherActiveProf <- setNetworkProfile prof
  case eitherActiveProf of
    Right activeProf -> Right <$> (modifySystemState (\p -> let lastProfile = currentNetworkProfile p
                                                            in  p { previousNetworkProfile = lastProfile,
                                                                    currentNetworkProfile = activeProf  }) )
    Left err -> return $ Left err
  



checkForConnection
  :: (Monad m, PingSyncNetworkEff m, HasTimer m) =>
     Ord (Tick m) => 
     SystemState m -> m (Either SystemError (SystemState m))
checkForConnection st = loop 
  where
    loop = do
      conn <- getStatus
      case conn of 
        Connected -> return $ Right st
        Unconnected -> do
                eitherTime <- getTick
                case eitherTime of
                   Left err -> return $ Left err
                   Right time
                      |time >= timeout st -> do
                                    erslt <- setNetworkState Timeout
                                    case erslt of
                                     Left err -> return $ Left err
                                     Right _ -> return $ Right st
                      |otherwise -> loop 
          
  


runSystemIO :: IO () 
runSystemIO = putStrLn "System Started"
  

  
