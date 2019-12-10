module Test.Info2.Cyp.Typing.Proof where

import Text.PrettyPrint (hcat, text)

import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Types

typeCheckEqnSeq :: [Assump] -> EqnSeq Term -> TI ()
typeCheckEqnSeq as eqns = do
    -- TVars for start (TODO: RESPECT FIXES)
    asStart <- traverse varToAssump $ getVars start
    let as' = as ++ asStart
    foldl (tcEqnStep as') (return start) eqns
    return ()
    where
        varToAssump :: Id -> TI Assump
        varToAssump x = do
            v <- newTVar Star
            return $ x :>: toScheme v

        start = eqnSeqHead eqns

        -- TODO: CLEANER! (TI TERM?)
        tcEqnStep :: [Assump] -> TI Term -> Term -> TI Term
        tcEqnStep as tiLhs rhs = do
            termLhs <- tiLhs
            tLhs <- tiTerm as termLhs
            tRhs <- tiTerm as rhs
            unifyWithErrMsg tLhs tRhs $ errMsg termLhs rhs
            return rhs

        -- TODO: Cleaner error message
        errMsg lhs rhs = capIndent
            "While typechecking a step in an equation sequence"
            [ hcat 
                [ unparseTermPretty lhs
                , text " .=. "
                , unparseTermPretty rhs ]]