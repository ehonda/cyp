module Test.Info2.Cyp.Typing.Theory where

import Control.Monad

import Test.Info2.Cyp.Typing.Inference
--import Test.Info2.Cyp.Env
import Test.Info2.Cyp.Types

-- Might be moved into Types.hs
--data TypeEnv = TypeEnv
--    { 
--
--    }

--tiEnv :: [Assump] -> Env -> [Assump]
--tiEnv as env = runTI $ do
    -- Step 1: Infer type Assumptions for constructors

type FunAlts = Named [Alt]
    
--inferFunctionTypes :: [DataType] -> [FunAlts] -> [Named Type]
inferFunctionTypes dts fs = runTI $ do
    -- Make fresh type vars for tiAlts
    funTVs <- replicateM (length fs) $ newTVar Star
    let altsTVs = zip (map namedVal fs) funTVs
    mapM (\(alts, tvs) -> tiAlts [] alts tvs) altsTVs
    return altsTVs
    where
        dcons = concat $ map dtConss dts