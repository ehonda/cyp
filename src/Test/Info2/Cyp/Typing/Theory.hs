module Test.Info2.Cyp.Typing.Theory where

import Prelude hiding ((<>))
import Control.Monad (mapM, mapM_, replicateM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import Data.Either (lefts, rights)
import Data.List (find, nub)
import qualified Data.List.NonEmpty as NL
import Data.Maybe (fromMaybe)
import Text.PrettyPrint (Doc, text, (<>), ($$), hcat, vcat, nest)

import Algebra.Graph.AdjacencyMap
import Algebra.Graph.AdjacencyMap.Algorithm
import qualified Algebra.Graph.NonEmpty.AdjacencyMap as NG

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


-- TODO: MOVE TO ANOTHER PLACE?
--data Binding = Expl ExplicitBinding | Impl ImplicitBinding 
--    deriving (Eq, Show)
--
--prettyBinding :: Binding -> String
--prettyBinding (Expl b) = prettyExplicitBinding b
--prettyBinding (Impl b) = prettyImplicitBinding b

toBindings :: [FunctionAlts] -> [Assump] 
    -> ([ExplicitBinding], [ImplicitBinding])
toBindings funAlts sigs = (expls, impls)
    where
        defaultToImplicit :: FunctionAlts -> 
            Either ExplicitBinding ImplicitBinding
        defaultToImplicit f@(id, alts) = fromMaybe (Right f) $
            fmap (\sig -> Left (sig, alts)) $
                find (hasName id) sigs

        expls = lefts $ map defaultToImplicit funAlts
        impls = rights $ map defaultToImplicit funAlts

                
--data DGVertex = Expl Id | Impl Id deriving (Eq, Ord, Show)
-- TODO: USE EITHER HERE
data DGVertex 
    = Expl ExplicitBinding 
    | Impl ImplicitBinding 
    deriving (Eq, Ord, Show)

--vertexName :: DGVertex -> Id
--vertexName (Expl (x :>: _, _)) = x
--vertexName (Impl (x, _)) = x

vertexAlts :: DGVertex -> [Alt]
vertexAlts (Expl (_, alts)) = alts
vertexAlts (Impl (_, alts)) = alts

type DependencyGraph = AdjacencyMap DGVertex

dependencies :: [Id] -> [Alt] -> [Id]
dependencies dconNames alts = nub $ concat $ map depList alts
    where
        isNotDataCons :: Id -> Bool
        isNotDataCons x = not $ x `elem` dconNames

        depList :: Alt -> [Id]
        depList (_, rhs) = filter isNotDataCons $ constSymbols rhs

makeDependencyGraph :: ([ExplicitBinding], [ImplicitBinding]) -> 
    [Id] -> DependencyGraph
makeDependencyGraph (expls, impls) dconNames = edges $ explEdges ++ implEdges
    where
        toVertex :: Id -> DGVertex
        --toVertex x = fromMaybe (Impl x) $ 
        --    fmap (Expl . assumpName) $
        --        find (hasName x) $ map fst expls
        toVertex x = v
            where
                mbExpl = find (hasName x . fst) expls
                mbImpl = find ((x ==) . fst) impls

                -- If x is found neither in expls nor impls,
                -- its is an unbound identifier, which will be
                -- noticed later (TODO: UGLY, IS THERE A BETTER WAY?)
                v = case mbExpl of
                    Just bind -> Expl bind
                    Nothing -> fromMaybe (Impl (x, [])) $ fmap Impl mbImpl

        --makeEdges :: (DGVertex, [Alt]) -> [(DGVertex, DGVertex)]
        --makeEdges (vertex, alts) = zip (repeat vertex) $ 
        --    map toVertex $ dependencies dconNames alts
        makeEdges :: DGVertex -> [(DGVertex, DGVertex)]
        makeEdges v = zip (repeat v) $ map toVertex $ 
            dependencies dconNames $ vertexAlts v

        explEdges = concat $ map makeEdges $ map Expl expls
        implEdges = concat $ map makeEdges $ map Impl impls
        --explEdges = concat $ map makeEdges $ map toExplAndAlts expls
        --    where
        --        toExplAndAlts ((i :>: _), alts) = (toVertex i, alts)
--
        --implEdges = concat $ map makeEdges $ map toImplAndAlts impls
        --    where
        --        toImplAndAlts (i, alts) = (toVertex i, alts)


--makeBindGroups :: DependencyGraph -> [BindGroup]
makeBindGroups graph = groups
    where
        -- Since SCC gives an acylcic graph,
        -- topSort will always succeed
        sortedSCCs = fromMaybe [] $
            fmap reverse $ topSort $ scc graph

        isExpl, isImpl :: DGVertex -> Bool
        isExpl (Expl _) = True
        isExpl _ = False
        isImpl = not . isExpl

        -- Convert SCCs to bind groups. We do
        -- this by simply putting all expls in one list
        -- and all impls in another, even if a more refined
        -- decomposition is available, since this implements
        -- the semantics demanded in the haskell report
        -- (see also typing haskell in haskell)
        --toBindGroup :: NG.AdjacencyMap DGVertex -> BindGroup
        toBindGroup s = (expls, [impls])
            where
                -- If either is empty (Nothing), it is natural
                -- to return []
                explVertices = fromMaybe [] $ 
                    (fmap (NL.toList . NG.vertexList1)) $
                    NG.induce1 isExpl s

                implVertices = fromMaybe [] $ 
                    (fmap (NL.toList . NG.vertexList1)) $
                    NG.induce1 isImpl s

                toExpl (Expl x) = x
                toImpl (Impl x) = x

                expls = map toExpl explVertices
                impls = map toImpl implVertices

        groups = map toBindGroup sortedSCCs


--inferFunctionTypes :: Env -> TI [Assump]
--inferFunctionTypes env = do
--    -- Make fresh type variables for the types
--    -- of the functions
--    funTypes <- replicateM (length funNames) $ newTVar Star
--
--    -- Make assumptions about these function types to be passed
--    -- in to tiAlts, because term type inference on the rhs may
--    -- need these e.g. in the recursive function:
--    --      length (x:xs) = 1 + length xs
--    -- term type inference for the rhs needs to know about length's
--    -- type. The schemes here are unqualified
--    let funAs = zipWith (:>:) funNames $ map toScheme funTypes
--        as = consAs ++ funAs
--
--    -- Infer function types
--    mapM (\((_, alts), t) -> tiAlts as alts t) $
--        zip funAlts funTypes
--
--    -- Apply substitution to funTypes and quantify
--    -- over any type variables left, e.g.
--    --      g :: v4 -> v4
--    -- becomes
--    --      g :: forall v0. v0 -> v0
--    s <- getSubst
--    let subFunTypes = apply s funTypes
--        subAs = zipWith (:>:) funNames $ map quantifyAll subFunTypes
--    return subAs
--    where
--        consAs = getConsAssumptions $ datatypes env
--        funAlts = functionsAlts env
--        funNames = map fst $ funAlts


typeCheckFunctionsAlts :: Env -> TI [Assump]
typeCheckFunctionsAlts env = tiSeq tiBindGroup dconAs bindGroups
    where
        expls = explicitBindings env
        impls = implicitBindings env
        dconAs = getConsAssumptions $ datatypes env
        dconNames = map assumpName dconAs
            
        depGraph = makeDependencyGraph (expls, impls) dconNames
        bindGroups = makeBindGroups depGraph
    ---- Infer function types first 
    --inferredFunAs <- inferFunctionTypes env
--
    ---- Check if inferred types agree with provided
    ---- type signatures
    --lift $ mapM_ checkAgainstSig inferredFunAs
    --return inferredFunAs
    --where
    --    typeSigs = typeSignatures env
    --    
    --    checkAgainstSig :: Assump -> ErrT ()
    --    checkAgainstSig a = case find (nameEq a) typeSigs of
    --        Just sig -> if a /= sig
    --            then throwE $ errMsg a sig
    --            else return ()
    --        Nothing -> return ()
--
    --    errMsg :: Assump -> Assump -> Doc
    --    errMsg a@(f :>: _) sig = capIndent 
    --        (concat 
    --            [ "Inferred type of "
    --            , f
    --            , " is incompatible with its type signature:"])
    --        [ (text "expected = ") <> assumpDoc sig
    --        , (text "inferred = ") <> assumpDoc a]


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