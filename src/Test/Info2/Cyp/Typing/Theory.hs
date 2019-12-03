module Test.Info2.Cyp.Typing.Theory where

import Control.Monad (mapM, mapM_)
import Data.List (find)
import Data.Maybe (fromMaybe)

import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Util

-- Typecheck Theory
--------------------------------------------------

getTheoryAssumps :: Env -> Err [Assump]
getTheoryAssumps env = do
    let consAs = getConsAssumptions $ datatypes env
    funAs <- runTI $ typeCheckFunctionsAlts env
    return (consAs ++ funAs)


typeCheckFunctionsAlts :: Env -> TI [Assump]
typeCheckFunctionsAlts env = do
    -- Make type variables for the function types or use
    -- proved type signature if there is any
    funTypes <- mapM expectedType funNames

    -- We need assumptions about these function types to be passed
    -- in to tiAlts, because term type inference on the rhs may
    -- need these e.g. in the recursive function:
    --      length (x:xs) = 1 + length xs
    -- term type inference for the rhs needs to know about length's
    -- type. The assumptions should be unqualified, if there
    -- is no type signature for the function i.e.
    --      g :>: Forall [] v0
    -- instead of 
    --      g :>: Forall [Star] (TGen 0)
    -- If there is a type signature, we use that instead (can
    -- be qualified)
    let expSchemes = map toScheme funTypes
        expAs = zipWith (:>:) funNames expSchemes

        defaultToTypeSig :: Assump -> Assump
        defaultToTypeSig a = fromMaybe a $ find 
            (nameEq a) funSigs

        funAs = map defaultToTypeSig expAs
        as = consAs ++ funAs

    -- Typecheck and infer functions
    mapM (\((_, alts), t) -> tiAlts as alts t) $ 
        zip funAlts funTypes

    -- Apply substitution to funTypes and return
    -- either the provided type sig or the all-
    -- quantified inferred type. At this point we can
    -- quantify over any type variables left, e.g.
    --      g :: v4 -> v4
    -- becomes
    --      g :: forall v0. v0 -> v0
    s <- getSubst
    let subFunTypes = apply s funTypes
        subAs = zipWith (:>:) funNames $ map quantifyAll subFunTypes
        finalAs = map defaultToTypeSig subAs
    return finalAs
    where
        consAs = getConsAssumptions $ datatypes env

        funAlts = functionsAlts env
        funNames = map fst $ functionsAlts env
        funSigs = typeSignatures env

        expectedType :: Id -> TI Type
        expectedType f = 
            case find (\(n :>: _) -> n == f) funSigs of
                Just (_ :>: sc) -> freshInst sc
                Nothing -> newTVar Star


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