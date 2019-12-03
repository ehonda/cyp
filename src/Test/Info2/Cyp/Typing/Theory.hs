module Test.Info2.Cyp.Typing.Theory where

import Prelude hiding ((<>))
import Control.Monad (mapM, mapM_, replicateM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import Data.List (find)
import Text.PrettyPrint (Doc, text, (<>), ($$), hcat, vcat, nest)

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

inferFunctionTypes :: Env -> TI [Assump]
inferFunctionTypes env = do
    -- Make fresh type variables for the types
    -- of the functions
    funTypes <- replicateM (length funNames) $ newTVar Star

    -- Make assumptions about these function types to be passed
    -- in to tiAlts, because term type inference on the rhs may
    -- need these e.g. in the recursive function:
    --      length (x:xs) = 1 + length xs
    -- term type inference for the rhs needs to know about length's
    -- type. The schemes here are unqualified
    let funAs = zipWith (:>:) funNames $ map toScheme funTypes
        as = consAs ++ funAs

    -- Infer function types
    mapM (\((_, alts), t) -> tiAlts as alts t) $
        zip funAlts funTypes

    -- Apply substitution to funTypes and quantify
    -- over any type variables left, e.g.
    --      g :: v4 -> v4
    -- becomes
    --      g :: forall v0. v0 -> v0
    s <- getSubst
    let subFunTypes = apply s funTypes
        subAs = zipWith (:>:) funNames $ map quantifyAll subFunTypes
    return subAs
    where
        consAs = getConsAssumptions $ datatypes env
        funAlts = functionsAlts env
        funNames = map fst $ funAlts


typeCheckFunctionsAlts :: Env -> TI [Assump]
typeCheckFunctionsAlts env = do
    -- Infer function types first 
    inferredFunAs <- inferFunctionTypes env

    -- Check if inferred types agree with provided
    -- type signatures
    lift $ mapM_ checkAgainstSig inferredFunAs
    return inferredFunAs
    where
        typeSigs = typeSignatures env
        
        checkAgainstSig :: Assump -> ErrT ()
        checkAgainstSig a = case find (nameEq a) typeSigs of
            Just sig -> if a /= sig
                then throwE $ errMsg a sig
                else return ()
            Nothing -> return ()

        errMsg :: Assump -> Assump -> Doc
        errMsg a@(f :>: _) sig = capIndent 
            (concat 
                [ "Inferred type of "
                , f
                , " is incompatible with its type signature:"])
            [ (text "expected = ") <> assumpDoc sig
            , (text "inferred = ") <> assumpDoc a]


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