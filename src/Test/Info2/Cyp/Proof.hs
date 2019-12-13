module Test.Info2.Cyp.Proof where

import Control.Monad.State

import Test.Info2.Cyp.Env
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types

toInterpretedEqns :: EqnSeqq RawTerm -> Env -> (EqnSeqq Term, Env)
toInterpretedEqns reqns env = runState 
    (traverse (state . declareTerm) reqns) env