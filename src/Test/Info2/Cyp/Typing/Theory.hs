module Test.Info2.Cyp.Typing.Theory where

import Control.Monad

import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Types

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

typeCheckProp :: [Assump] -> Prop -> TI (Type, Type)
typeCheckProp as (Prop lhs rhs) = do
    -- Tvars need to be created for all Schematics on the lhs
    let (head, tail) = stripComb lhs
        strippedLhs = head : tail

        isSchematic (Schematic _) = True
        isSchematic _ = False

        schematicToAssump (Schematic (x, _)) = do
            v <- newTVar Star
            return $ x :>: toScheme v

        schematicsLhs = filter isSchematic strippedLhs
    
    -- Unify left and right hand sides types
    asLhs <- traverse schematicToAssump schematicsLhs
    let as' = as ++ asLhs
    tLhs <- tiTerm as' lhs

    tRhs <- tiTerm as' rhs
    unify tLhs tRhs
    
    -- Apply subsitution
    s <- getSubst
    return (apply s tLhs, apply s tRhs)