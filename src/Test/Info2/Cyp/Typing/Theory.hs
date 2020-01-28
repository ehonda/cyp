module Test.Info2.Cyp.Typing.Theory where

import Data.Either (lefts, rights)
import Data.List (find, nub)
import qualified Data.List.NonEmpty as NL
import Data.Maybe (fromMaybe)
import Text.PrettyPrint (text)

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
    funAs <- runTI $ typeCheckBindings env
    return (consAs ++ funAs)

-- TODO: MOVE TO ANOTHER PLACE?
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


-- TODO: USE EITHER HERE
data DGVertex 
    = Expl ExplicitBinding 
    | Impl ImplicitBinding 
    deriving (Eq, Ord, Show)

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

makeDependencyGraph :: [ExplicitBinding] -> [ImplicitBinding] -> 
    [Id] -> DependencyGraph
makeDependencyGraph expls impls dconNames = overlay
    (vertices $ explVertices ++ implVertices)
    (edges $ explEdges ++ implEdges)
    where
        toVertex :: Id -> DGVertex
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

        makeEdges :: DGVertex -> [(DGVertex, DGVertex)]
        makeEdges v = zip (repeat v) $ map toVertex $ 
            dependencies dconNames $ vertexAlts v

        explVertices, implVertices :: [DGVertex]
        explVertices = map Expl expls
        implVertices = map Impl impls

        explEdges, implEdges :: [(DGVertex, DGVertex)]
        explEdges = concat $ map makeEdges explVertices
        implEdges = concat $ map makeEdges implVertices

makeBindGroups :: DependencyGraph -> [BindGroup]
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
        toBindGroup :: NG.AdjacencyMap DGVertex -> BindGroup
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


typeCheckBindings :: Env -> TI [Assump]
typeCheckBindings env = tiSeq tiBindGroup dconAs bindGroups
    where
        expls = explicitBindings env
        impls = implicitBindings env
        dconAs = getConsAssumptions $ datatypes env
        dconNames = map assumpName dconAs
            
        depGraph = makeDependencyGraph expls impls dconNames
        bindGroups = makeBindGroups depGraph

typeCheckProp :: [Assump] -> Prop -> TI (Type, Type)
typeCheckProp as p@(Prop lhs rhs) = withErrorContext errContext $ do
    -- Unify left and right hand sides types
    -- Need assumps for vars on lhs and rhs
    asVars <- traverse newVarAssump $ getVarsProp p
    let as' = as ++ asVars
    tLhs <- tiTerm as' lhs
    tRhs <- tiTerm as' rhs
    unify tLhs tRhs

    -- Apply subsitution
    s <- getSubst
    return (apply s tLhs, apply s tRhs)
    where
        --errMsg = capIndent
        errContext = capIndent
            "While typechecking the proposition:"
            [unparsePropPretty p]

data TheoryTypeInfo = TheoryTypeInfo 
    { ttiAssumps :: [Assump]
    , ttiAxiomsTypes :: [(Prop, (Type, Type))]
    , ttiGoalsTypes :: [(Prop, (Type, Type))]
    }

printTheoryTypeInfo tinfo = do
    -- Print theory assumptions
    printHeader "THEORY ASSUMPTIONS"
    mapM_ putStrLn $ map prettyAssump $ ttiAssumps tinfo

    -- Print axioms and their types
    printHeader "PROPS AND TYPES"
    let prettyTypes (t, s) = (prettyType t, prettyType s)
        axs = [ax | (ax, _) <- ttiAxiomsTypes tinfo]
        axiomTypes = [ts | (_, ts) <- ttiAxiomsTypes tinfo]
    mapM_ (putStrLn . show) $ zip axs $ map prettyTypes axiomTypes
    
    -- Print goals and their types
    printHeader "GOALS AND TYPES"
    let gls = [g | (g, _) <- ttiGoalsTypes tinfo]
        goalTypes = [ts | (_, ts) <- ttiGoalsTypes tinfo]
    mapM_ (putStrLn . show) $ zip gls $ map prettyTypes goalTypes

    where
        printHeader h = mapM_ putStrLn ["", h, replicate 20 '-', ""]

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