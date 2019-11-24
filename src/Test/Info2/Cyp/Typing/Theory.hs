module Test.Info2.Cyp.Typing.Theory where

import Control.Monad

import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Types

--type FunAlts = Named [Alt]
    
--inferFunctionTypes :: [DataType] -> [FunAlts] -> [Named Type]
--inferFunctionTypes dts fs = runTI $ do
--    -- Make fresh type vars for tiAlts
--    funTVs <- replicateM (length fs) $ newTVar Star
--    let funsAndTVs = zip fs funTVs
--    mapM (\(Named _ alts, tvs) -> tiAlts dcAssumps alts tvs) funsAndTVs
--    s <- getSubst
--    let funTypes = map 
--            (\(namedFun, tv) -> Named (namedName namedFun) (apply s tv))
--            funsAndTVs
--    return funTypes
--    --return funsAndTVs
--    where
--        dcons = concat $ map dtConss dts
--        dcAssumps = map 
--            (\(dcName, dcType) -> dcName :>: quantifyAll dcType)
--            dcons


-- Typecheck Theory
--------------------------------------------------

getTheoryAssumps env =
    let consAs = getConsAs env
        funAs = getFunAs consAs env
    in consAs ++ funAs
    where
        -- Constructors
        -----------------------------------------------------------
        getConsAs env = map (\(n, t) -> n :>: quantifyAll t) dcons
            where
                dcons = concat $ map dtConss $ datatypes env

        -- Functions
        -----------------------------------------------------------
        getFunAs consAs env = runTI $ do
            -- Make tvars for the types of the functions
            funsTVs <- replicateM (length funsAlts) $ newTVar Star

            -- Typecheck and infer functions
            mapM (\((_, alts), tv) -> tiAlts consAs alts tv) $ 
                zip funsAlts funsTVs

            -- Substitute and generate assumptions for functions
            s <- getSubst
            let funTypes = map (apply s) funsTVs
                funSchemes = map quantifyAll funTypes
                funAs = zipWith (:>:) 
                    [name | (name, _) <- funsAlts] 
                    funSchemes
            return funAs
            where
                funsAlts = functionsAlts env

typeCheckTheory env = do
    typeCheckAxioms
    typeCheckGoals
    where
        as = getTheoryAssumps env
        axs = axioms env
        gls = goals env

        typeCheckAxioms = mapM 
            (\(Named _ p) -> typeCheckProp as p)
            axs
        typeCheckGoals = mapM (typeCheckProp as) gls

typeCheckProp :: [Assump] -> Prop -> TI ()
typeCheckProp as (Prop lhs rhs) = do
    tLhs <- tiTerm as lhs
    tRhs <- tiTerm as rhs
    unify tLhs tRhs