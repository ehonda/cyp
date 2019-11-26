module Test.Info2.Cyp.Typing.Theory where

import Control.Monad

import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Types

-- Typecheck Theory
--------------------------------------------------

getTheoryAssumps env =
    let consAs = getConsAssumptions $ datatypes env
        funAs = getFunAs consAs env
    in consAs ++ funAs
    where
        getFunAs consAs env = runTI $ do
            -- 
            -- Make tvars for the types of the functions
            funsTVs <- replicateM (length funsAlts) $ newTVar Star

            -- Make assumptions (f :>: tv_f), for recursive functions
            -- TODO: REWRITE REST OF FUNCTION TO USE THIS
            let funAs = zipWith (:>:) 
                    [name | (name, _) <- funsAlts] $
                    map toScheme funsTVs

            -- Typecheck and infer functions
            mapM (\((_, alts), tv) -> tiAlts (consAs ++ funAs) alts tv) $ 
                zip funsAlts funsTVs

            -- Substitute and generate assumptions for functions
            s <- getSubst
            let funTypes = map (apply s) funsTVs
                funSchemes = map quantifyAll funTypes
                funAs' = zipWith (:>:) 
                    [name | (name, _) <- funsAlts] 
                    funSchemes
            return funAs'
            where
                funsAlts = functionsAlts env

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

typeCheckTheory env = TheoryTypeInfo
        { ttiAssumps = as
        , ttiAxiomsTypes = zip axs $ axiomsTypes
        , ttiGoalsTypes = zip gls $ goalTypes
        }
    where
        as = getTheoryAssumps env
        axs = [a | Named _ a <- axioms env]
        axiomsTypes = map (\p -> runTI $ typeCheckProp as p) axs
        gls = goals env
        goalTypes = map (\p -> runTI $ typeCheckProp as p) gls