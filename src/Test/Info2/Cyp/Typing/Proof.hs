module Test.Info2.Cyp.Typing.Proof where

import Control.Monad (forM_)

import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Types

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

-- TC for different types of proofs
---------------------------------------------------------

--typeCheckProof :: [Assump] -> ParseProof -> TI ()
--typeCheckProof as (ParseEquation eqns) = typeCheckEqnSeqq as eqns