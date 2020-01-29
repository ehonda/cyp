module Test.Info2.Cyp.Typing.Proof where

import Control.Monad (forM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.List (nub)
import Data.Maybe

import Test.Info2.Cyp.Parser
import Test.Info2.Cyp.Proof
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Typing.Theory
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Util

-- REMOVE: ONLY FOR TESTING
import Text.PrettyPrint




-- Proofcheck state
---------------------------------------------------------

-- State is (current assumptions, error stack)
type ProofTCState = ([Assump], [Doc])
emptyErrorsWith :: [Assump] -> ProofTCState
emptyErrorsWith as = (as, [])

type ProofTC = StateT ProofTCState ErrT

runProofTC :: [Assump] -> ProofTC a -> Err a
runProofTC as f = runExcept $ evalStateT f $ emptyErrorsWith as

-- Just for clearer naming
noAction :: ProofTC ()
noAction = return ()

-- This version doesn't apply runExcept, so we can stay inside
-- ErrT a
runTI' :: TI a -> ErrT a
runTI' f = evalStateT f nullTIState

addAssump :: Assump -> ProofTC ()
addAssump a = modify $ (\(as, es) -> (a : as, es))

getAssumps :: ProofTC [Assump]
getAssumps = gets fst

ptcGetErrorContexts :: ProofTC [Doc]
ptcGetErrorContexts = gets snd

-- Error context handling, some duplication from inference
ptcWithErrorContexts :: [Doc] -> ProofTC a -> ProofTC a
ptcWithErrorContexts errs tc = do
    es <- ptcGetErrorContexts
    addErrorContexts errs
    res <- tc
    restoreErrorContextStack es
    return res
    where
        addErrorContexts :: [Doc] -> ProofTC ()
        addErrorContexts errs = modify $ 
            \(as, es) -> (as, es ++ errs)

        restoreErrorContextStack :: [Doc] -> ProofTC ()
        restoreErrorContextStack es = modify $
            \(as, _) -> (as, es)

ptcWithErrorContext :: Doc -> ProofTC a -> ProofTC a
ptcWithErrorContext err = ptcWithErrorContexts [err]

-- Lifts TI to PTC and uses err ctxt stack
liftTI :: TI a -> ProofTC a
liftTI ti = do
    es <- ptcGetErrorContexts
    lift $ runTI' $ withErrorContexts es ti


-- TYPECHECK FOR PROOFS
------------------------------------------------------------
typeCheckLemma :: ParseLemma -> ProofTC ()
typeCheckLemma (ParseLemma name rawProp proof) = do
    as <- getAssumps
    ptcWithErrorContext errContext $ ptcProp as rawProp
    typeCheckProof proof
    where
        errContext = text "Checking Lemma"


typeCheckProof :: ParseProof -> ProofTC ()
typeCheckProof (ParseEquation reqns) = 
    typeCheckEquationalProof reqns
typeCheckProof (ParseExt withSig rprop proof) =
    typeCheckExtensionalProof withSig rprop proof
typeCheckProof (ParseCases overSc overTerm cases) = 
    typeCheckCasesProof overSc overTerm cases
typeCheckProof (ParseInduction _ _ cases) =
    typeCheckCases cases

typeCheckEquationalProof :: EqnSeqq RawTerm -> ProofTC ()
typeCheckEquationalProof reqns = do
    as <- getAssumps
    ptcWithErrorContext errContext $ liftTI $
        tiEquations as eqns
    where
        errContext = text "Type checking equational proof"

        eqns = fmap interpretTermDefault reqns

        tiEquations :: [Assump] -> EqnSeqq Term -> TI ()
        tiEquations as eqns = do
            -- Make new tvs and assumptions for the vars
            -- Do we need kind inference here?
            -- Putting as' at the end ensures we don't overwrite
            -- old assumptions
            as' <- traverse newVarAssump $ getVarsEqnSeqq eqns
            typeCheckEqnSeqq (as ++ as') eqns

typeCheckExtensionalProof :: Assump -> RawProp -> ParseProof -> ProofTC ()
typeCheckExtensionalProof varAssump rawProp proof = do
    -- Add assumptions about ext var
    addAssump varAssump
    as <- getAssumps

    -- Typecheck to show
    ptcWithErrorContext errToShow $ ptcProp as rawProp
    
    typeCheckProof proof
    where
        errToShow :: Doc
        errToShow = capIndent 
            "While checking 'To Show:' under the assumption:"
            [assumpDoc varAssump]


typeCheckCasesProof :: Scheme -> RawTerm -> [ParseCase] -> ProofTC ()
typeCheckCasesProof overSc overRawTerm cases = ptcWithErrorContext errCases $ do
    -- Check that overTerm has the right type
    -- eg (p x) :: Bool
    as <- getAssumps
    liftTI $ tiOver as
    typeCheckCases cases
    where
        errCases = hsep 
            [ text "While typechecking case analysis on"
            , unparseRawTerm overRawTerm
            , text "::"
            , text $ prettyScheme overSc
            ]

        overTerm = interpretTermDefault overRawTerm

        tiOver :: [Assump] -> TI ()
        tiOver as = do
            -- Generate tvs for unbounds
            as' <- traverse newVarAssump $ getVars overTerm
            t <- tiTerm (as ++ as') overTerm
            t' <- freshInst overSc
            unify t t'

-- Cases should be independet, so we restore the
-- state after each case check (they fix new frees)
typeCheckCases :: [ParseCase] -> ProofTC ()
typeCheckCases cases = do
    originalState <- get
    mapM_ (\c -> typeCheckCase c >> (put originalState)) cases    


typeCheckCase :: ParseCase -> ProofTC ()
typeCheckCase pcase = ptcWithErrorContext errCase $ do
    -- Need to add fixes to assumps
    mapM_ addAssump $ fromMaybe [] $ pcFixs pcase
    as <- getAssumps

    -- Typecheck to show
    maybe noAction (\p -> ptcWithErrorContext errToShow $ ptcProp as p) $ 
        pcToShow pcase

    -- Typecheck assumps
    let assumps = map (snd . namedVal) $ pcAssms pcase
    mapM_ (\p -> ptcWithErrorContext errAssumps $ ptcProp as p) assumps

    typeCheckProof $ pcProof pcase

    where
        errCase = hsep 
            [ text "While typechecking the case"
            , quotes $ unparseRawTerm $ pcCons pcase
            ]
        errToShow = text "While typechecking 'To Show:'"
        errAssumps = text "While typechecking assumptions:"


--------------------------------------------------------------
-- Typecheck for props and equation sequences

-- Props
tiRawProp :: [Assump] -> RawProp -> TI ()
tiRawProp as p = do
    typeCheckProp as $ interpretPropDefault p
    return ()

ptcProp :: [Assump] -> RawProp -> ProofTC ()
ptcProp as p = liftTI $ tiRawProp as p


-- Equations/Equation Sequences
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
checkTypeOfTermIs as t term = withErrorContext errContext $ do
    t' <- tiTerm as term
    unify t t'
    where
        errContext = capIndent
            "While checking the type of a term:"
            [termDoc "term" term]