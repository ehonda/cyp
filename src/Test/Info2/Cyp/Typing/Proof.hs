module Test.Info2.Cyp.Typing.Proof where

import Control.Monad (forM_)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)

import Test.Info2.Cyp.Parser
import Test.Info2.Cyp.Proof
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Util

-- TODO: PROVIDE MORE DETAILED ERROR MESSAGES
typeCheckEquations :: (Traversable t) => [Assump] -> Type -> t Term -> TI ()
typeCheckEquations as t eqns = forM_ eqns $ checkTypeOfTermIs as t

typeCheckEqnSeq :: [Assump] -> EqnSeq Term -> TI ()
typeCheckEqnSeq as eqns = do
    t <- tiTerm as start
    typeCheckEquations as t eqns
    where
        start = eqnSeqHead eqns

typeCheckEqnSeqq :: [Assump] -> EqnSeqq Term -> TI ()
typeCheckEqnSeqq as eqns = do
    t <- tiTerm as start
    typeCheckEquations as t eqns
    where
        start = eqnSeqqHead eqns

checkTypeOfTermIs :: [Assump] -> Type -> Term -> TI ()
checkTypeOfTermIs as t term = do
    t' <- tiTerm as term
    unifyWithErrMsg t t' $ errMsg
    where
        errMsg = capIndent
            "While checking the type of a term:"
            [termDoc "term" term]

-- Proofcheck state
---------------------------------------------------------

-- Duplication here, interpretation is also done in Env.hs
-- but there it is mixed with also updating the environment,
-- we would like to have that separated here as we don't need
-- the whole environment
type FixesMap = M.Map String Integer    -- TODO: MOVE TO TYPES.hs

interpretTermPTC :: FixesMap -> RawTerm -> Term
interpretTermPTC fixes rt = fmap defaultToZero rt
    where
        defaultToZero var = fromMaybe (var, 0) $ 
            fmap (\n -> (var, n)) $ M.lookup var fixes 


type ProofTCState = ([Assump], FixesMap)
emptyFixesWith :: [Assump] -> ProofTCState
emptyFixesWith as = (as, M.empty)

type ProofTC = StateT ProofTCState ErrT

runProofTC :: [Assump] -> ProofTC a -> Err a
runProofTC as f = runExcept $ evalStateT f $ emptyFixesWith as

getAssumps :: ProofTC [Assump]
getAssumps = gets fst

-- Corresponds to declareTerm
-- Inserts unfixed vars at 0, eg x0
-- and leaves already fixed vars at n, eg xn
--fixFreesDefault :: RawTerm -> ProofTC ()
--fixFreesDefault rt =
--    where
--        ins free = M.insertWith (\_ n -> n) free 0

--typeCheckEquationalProof :: ParseProof -> ProofTC ()
--typeCheckEquationalProof (ParseEquation reqns) = do


-- TC for different types of proofs
---------------------------------------------------------

typeCheckProof :: [Assump] -> ParseProof -> Env -> TI ()
typeCheckProof as (ParseEquation reqns) env = do
    -- Kind inference needed here?
    as' <- traverse newVarAssump $ getVars start
    typeCheckEqnSeqq (as' ++ as) eqns
    where
        -- We interpret the equations and generate
        -- assumptions for all vars in the head
        -- of the sequence
        eqns = fst $ toInterpretedEqns reqns env
        start = eqnSeqqHead eqns