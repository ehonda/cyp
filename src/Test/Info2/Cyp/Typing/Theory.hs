module Test.Info2.Cyp.Typing.Theory where

import Control.Monad
import qualified Data.List as L
import Data.Maybe

import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Util

-- Typecheck Theory
--------------------------------------------------

getTheoryAssumps :: Env -> Err [Assump]
getTheoryAssumps env = do
    let consAs = getConsAssumptions $ datatypes env
    funAs <- getFunAs consAs env
    return (consAs ++ funAs)
    where
        getFunAs consAs env = runTI $ do
            -- Prepare function types for inference. If no type is
            -- specified, the type will be inferred with a new tvar
            --
            -- We can only infer types for functions that have been
            -- defined as well as declared (FunctionAlts exist),
            -- assumptions about the types of functions that are not
            -- declared (no FunctionAlts) are therefore ignored here  
            funTypes <- mapM expectedType funNames
            
            -- Make tvars for the types of the functions
            --funsTVs <- replicateM (length funsAlts) $ newTVar Star

            -- Make assumptions (f :>: tv_f), for recursive functions
            -- TODO: REWRITE REST OF FUNCTION TO USE THIS
            let funAs = (typeSignatures env) ++ 
                    (zipWith (:>:) funNames $ map toScheme funTypes)

            -- Typecheck and infer functions
            mapM (\((_, alts), t) -> tiAlts (consAs ++ funAs) alts t) $ 
                zip funsAlts funTypes

            -- Substitute and generate assumptions for functions
            s <- getSubst
            let funTypes' = map (apply s) funTypes
                funSchemes = map quantifyAll funTypes'
                funAs' = zipWith (:>:) 
                    funNames 
                    funSchemes
            return $ funAs' ++ typeSigs
            where
                funsAlts = functionsAlts env
                funNames = map fst funsAlts
                typeSigs = typeSignatures env
                
                expectedType f = case L.find (\(n :>: _) -> n == f) typeSigs of
                    Just (_ :>: sc) -> freshInst sc
                    Nothing -> newTVar Star
                --expectedType f = fromMaybe (newTVar Star) $
                --    fmap (\(_ :>: sc) -> freshInst sc) $
                --        find (\(n :>: _) -> n == f) $ typeSignatures env

typeCheckProp :: [Assump] -> Prop -> TI (Type, Type)
typeCheckProp as (Prop lhs rhs) = do
    -- Tvars need to be created for all Schematics on the lhs
    --      -> also for Free on lhs (goals are formulated with Free "x" (WHY?))
    let (head, tail) = stripComb lhs
        strippedLhs = head : tail

        getVars (Application a b) =
            (getVars a) ++ (getVars b)
        getVars (Free (x, _)) = [x]
        getVars (Schematic (x, _)) = [x]
        getVars _ = []

        -- Convert vars to assumps
        varToAssump x = do
            v <- newTVar Star
            return $ x :>: toScheme v

        --schematicsLhs = filter isSchematic strippedLhs
        varsLhs = concat $ map getVars strippedLhs

    -- Unify left and right hand sides types
    asLhs <- traverse varToAssump varsLhs
    let as' = as ++ asLhs
    tLhs <- tiTerm as' lhs

    tRhs <- tiTerm as' rhs
    -- UNIFY WITH ERR MSG ABOUT TERMS HERE
    unify tLhs tRhs
    
    -- Apply subsitution
    s <- getSubst
    return (apply s tLhs, apply s tRhs)

data TheoryTypeInfo = TheoryTypeInfo 
    { ttiAssumps :: [Assump]
    , ttiAxiomsTypes :: [(Prop, (Type, Type))]
    , ttiGoalsTypes :: [(Prop, (Type, Type))]
    }

printTheoryTypeInfo tinfo = do
    -- Print theory assumptions
    printHeader "THEORY ASSUMPTIONS"
    mapM_ print $ map prettyAssump $ ttiAssumps tinfo

    -- Print axioms and their types
    printHeader "PROPS AND TYPES"
    let prettyTypes (t, s) = (prettyType t, prettyType s)
        axs = [ax | (ax, _) <- ttiAxiomsTypes tinfo]
        axiomTypes = [ts | (_, ts) <- ttiAxiomsTypes tinfo]
    mapM_ print $ zip axs $ map prettyTypes axiomTypes
    
    -- Print goals and their types
    printHeader "GOALS AND TYPES"
    let gls = [g | (g, _) <- ttiGoalsTypes tinfo]
        goalTypes = [ts | (_, ts) <- ttiGoalsTypes tinfo]
    mapM_ print $ zip gls $ map prettyTypes goalTypes

    where
        printHeader h = mapM_ print ["", h, replicate 20 '-', ""]

typeCheckTheory :: Env -> Err TheoryTypeInfo
typeCheckTheory env = do
        as <- getTheoryAssumps env
        axiomsTypes <- mapM (\p -> runTI $ typeCheckProp as p) axs
        goalTypes <- mapM (\p -> runTI $ typeCheckProp as p) gls
        return $ TheoryTypeInfo
            { ttiAssumps = as
            , ttiAxiomsTypes = zip axs $ axiomsTypes
            , ttiGoalsTypes = zip gls $ goalTypes
            }
    where
        axs = [a | Named _ a <- axioms env]
        gls = goals env