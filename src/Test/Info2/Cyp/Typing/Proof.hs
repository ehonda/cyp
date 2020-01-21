module Test.Info2.Cyp.Typing.Proof where

import Control.Monad (forM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.List (nub)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)

import Test.Info2.Cyp.Parser
import Test.Info2.Cyp.Proof
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Typing.Theory
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

interpretTermWithFixes :: FixesMap -> RawTerm -> Term
interpretTermWithFixes fixes rt = fmap defaultToZero rt
    where
        defaultToZero var = fromMaybe (var, 0) $ 
            fmap (\n -> (var, n)) $ M.lookup var fixes

interpretRawPropWith :: FixesMap -> RawProp -> Prop
interpretRawPropWith fixes (Prop l r) =
    Prop (interp l) (interp r)
    where
        interp = interpretTermWithFixes fixes

type ProofTCState = ([Assump], FixesMap)
emptyFixesWith :: [Assump] -> ProofTCState
emptyFixesWith as = (as, M.empty)

type ProofTC = StateT ProofTCState ErrT

runProofTC :: [Assump] -> ProofTC a -> Err a
runProofTC as f = runExcept $ evalStateT f $ emptyFixesWith as

getAssumps :: ProofTC [Assump]
getAssumps = gets fst

getFixes :: ProofTC FixesMap
getFixes = gets snd

-- Corresponds to declareTerm
-- Inserts unfixed vars at 0, eg x0
-- and leaves already fixed vars at n, eg xn
fixFreesIfNew :: [String] -> ProofTC ()
fixFreesIfNew frees = modify $ \(as, fixes) -> (as, 
    foldl (\fixes v -> insertIfNotPresent v fixes) fixes frees)
    where
        insertIfNotPresent v = M.insertWith (\_ n -> n) v 0

fixRawTermFreesIfNew :: RawTerm -> ProofTC ()
fixRawTermFreesIfNew rt = fixFreesIfNew $ collectFrees rt []

-- Corresponds to variantFixes
-- Inserts unfixed vars at 0, eg x0
-- and incs already fixed vars at n, eg x_{n+1}
fixNewFrees :: [String] -> ProofTC ()
fixNewFrees frees = modify $ \(as, fixes) -> (as, 
    foldl (\fixes v -> insertNew v fixes) fixes frees)
    where
        insertNew v = M.insertWith (\_ n -> n + 1) v 0
        
fixRawTermNewFrees :: RawTerm -> ProofTC ()
fixRawTermNewFrees rt = fixNewFrees $ collectFrees rt []



-- TYPECHECK FOR PROOFS
------------------------------------------------------------

--exceptTI = lift $ except $ runTI

tiProp :: [Assump] -> Prop -> TI ()
tiProp as p = do
    as' <- traverse newVarAssump $ getVarsProp p
    typeCheckProp (as ++ as') p
    return ()

typeCheckLemma :: ParseLemma -> ProofTC ()
typeCheckLemma (ParseLemma name rawProp proof) = do
    -- We can typecheck the raw prop with default
    -- fixes, without modifying the state
    as <- getAssumps
    lift $ except $ runTI $ tiProp as $ 
        interpretRawPropDefault rawProp
    typeCheckProof proof
    where
        interpretRawPropDefault :: RawProp -> Prop
        interpretRawPropDefault (Prop l r) =
            Prop (interp l) (interp r)
            where
                interp = interpretTermWithFixes M.empty

typeCheckProof :: ParseProof -> ProofTC ()
typeCheckProof (ParseEquation reqns) = 
    typeCheckEquationalProof reqns
typeCheckProof (ParseExt rt rprop proof) =
    typeCheckExtensionalProof rt rprop proof

typeCheckEquationalProof :: EqnSeqq RawTerm -> ProofTC ()
typeCheckEquationalProof reqns = do
    fixes <- getFixes
    as <- getAssumps
    lift $ except $ runTI $ tiEquations as $ interpretEqnsWith fixes
    where
        interpretEqnsWith :: FixesMap -> EqnSeqq Term
        interpretEqnsWith fixes = 
            fmap (interpretTermWithFixes fixes) reqns

        tiEquations :: [Assump] -> EqnSeqq Term -> TI ()
        tiEquations as eqns = do
            -- Make new tvs and assumptions for the vars
            -- Do we need kind inference here?
            -- Putting as' at the end ensures we don't overwrite
            -- old assumptions
            as' <- traverse newVarAssump $ getVarsEqnSeqq eqns
            typeCheckEqnSeqq (as ++ as') eqns

typeCheckExtensionalProof :: RawTerm -> RawProp -> ParseProof -> ProofTC ()
typeCheckExtensionalProof fixTerm rawProp proof = do
    fixRawTermNewFrees fixTerm
    fixes <- getFixes
    as <- getAssumps
    lift $ except $ runTI $ tiProp as $ 
        interpretRawPropWith fixes rawProp
    typeCheckProof proof

--typeCheckCases :: String -> RawTerm -> [ParseCase] -> ProofTC ()
--typeCheckCases dtName rawTerm cases = do


typeCheckCase :: ParseCase -> ProofTC ()
typeCheckCase pcase = do
    -- variant fixes for case cons vars
    fixRawTermNewFrees $ pcCons pcase
    fixes <- getFixes
    as <- getAssumps

    -- typecheck goal
    --let action = \p -> except $ runTI $ 
    --        tiProp as $ interpretRawPropWith fixes p
--
    --lift $ fmap action $ pcToShow pcase

    -- convert assumps (necessary?)
    --

    typeCheckProof $ pcProof pcase


-- Utility
getVarsEqnSeqq :: EqnSeqq Term -> [String]
getVarsEqnSeqq eqns = nub $ concat $ fmap getVars eqns

getVarsProp :: Prop -> [String]
getVarsProp (Prop l r) = nub $ concat $ [getVars l, getVars r]