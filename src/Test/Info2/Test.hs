{-# LANGUAGE FlexibleContexts #-}

import Control.Monad.Trans.Except
import Control.Monad.State
import qualified Text.Parsec as Parsec
import Text.PrettyPrint.HughesPJ
import qualified Language.Haskell.Exts.Simple.Syntax as Exts
import qualified Language.Haskell.Exts.Simple.Parser as P
import Data.Either

import Test.Info2.Cyp.Blueprint.Blueprint
import Test.Info2.Cyp.Env
import Test.Info2.Cyp.Parser
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Typing.Theory
import Test.Info2.Cyp.Typing.Proof
import Test.Info2.Cyp.Util
import Test.Info2.Cyp

trivThy = "test-data/pos/trivial/cthy"
trivPrf = "test-data/pos/trivial/cprf"

revThy = "test-data/pos/revrev/cthy"
revPrf = "test-data/pos/revrev/cprf"

lenThy = "test-data/pos/length-append/cthy"
lenPrf = "test-data/pos/length-append/cprf"

wcThy = "test-data/no_unit/wildcard/cthy"

tcEasyThy = "test-data/no_unit/typecheck/easy/cthy"
tcEasyPrf = "test-data/no_unit/typecheck/easy/cprf"

tcWrongFunArgThy = "test-data/no_unit/typecheck/wrong_fun_arg/cthy"

tcLengthAppendThy = "test-data/no_unit/typecheck/length-append/cthy"
tcLengthAppendPrf = "test-data/no_unit/typecheck/length-append/cprf"

tcLengthSimpleThy = "test-data/no_unit/typecheck/length-simple/cthy"

ffThy = "test-data/pos/filter-filter/cthy"

tsWrongThy = "test-data/no_unit/typesig/wrong_sig/cthy"
tsRevRevThy = "test-data/no_unit/typesig/revrev/cthy"

tsDeclsymThy = "test-data/no_unit/typesig/declsym/cthy"

cthy base = base ++ "cthy"
cprf base = base ++ "cprf"

tiFunUnboundConsThy ="test-data/no_unit/ti-fun/unbound-cons-pat/cthy"

-- Contents of a typical Env, as extracted in processMasterFile
---------------------------------------------------------------

parseTransform content f = do
    result <- eitherToErr $ Parsec.parse cthyParser "" content
    f result

parseDataTypes c = parseTransform c readDataType

getEnv path = do
    thy <- readFile path
    case processMasterFile "thy" thy of
        Right env -> return env
        Left _ -> return declEnv


inspectProofFunc pthy pprf f = do
    thy <- readFile pthy
    prf <- readFile pprf
    case (processMasterFile "thy" thy) >>= (\env -> f prf env) of
        Left e -> print e
        Right r -> mapM_ print r





-- READ DATATYPE TESTS

dtTree = "Tree a = Leaf a | Node a (Tree a) (Tree a)"
dtWrapped = "Wrapped = WT (Int -> Int)"


-- (tycon : dacons) <- traverse parseCons $ splitStringAt "=|" s []
line1 s = traverse parseCons $ splitStringAt "=|" s []

{-- line1 dtTree:

Right 
    [Application (Const "Tree") (Free ("a",0))
    ,Application (Const "Leaf") (Free ("a",0))
    ,Application (Application (Application (Const "Node") (Free ("a",0))) (Application (Const "Tree") (Free ("a",0)))) (Application (Const "Tree") (Free ("a",0)))]
--}

-- tyname <- constName $ fst $ stripComb tycon
line2 s = do
    (tycon : dacons) <- traverse parseCons $ splitStringAt "=|" s []
    constName $ fst $ stripComb tycon


-- UTILITY FUNCTIONS
parseCons :: String -> Err Term
parseCons = iparseTerm (\x -> Right $ Free (x, 0))

constName (Const c) = return c
constName term = errStr $ "Term '" ++ show term ++ "' is not a constant."






-- TEST TYPECHECK FUNCTION ALTS
--------------------------------------------

tcFunEasy = "test-data/no_unit/tc-fun/easy/cthy"
tcFunConPatPoly = "test-data/no_unit/tc-fun/conpat-on-poly-fun/cthy"
tcFunDouble = "test-data/no_unit/tc-fun/double/cthy"

testTCBindings path = do
    env <- getEnv path
    return $ runTI $ typeCheckBindings env

prettyIOAssumps :: IO (Err [Assump]) -> IO (Err [String])
prettyIOAssumps = fmap (fmap (map prettyAssump))


-- MAKE DEP GRAPH
----------------------------------------

tcDepGraph3 = "test-data/no_unit/tc-fun/dep-graph/cthy"

testMakeDepGraph path = do
    env <- getEnv path
    return $ testMakeDepGraph' env

testMakeDepGraph' env = depGraph
--testMakeDepGraph' env = map prettyBindGroup bindGroups
    where
        dconNames = map assumpName $ 
            getConsAssumptions $ datatypes env

        expls = explicitBindings env
        impls = implicitBindings env

        depGraph = makeDependencyGraph expls impls dconNames

        bindGroups = makeBindGroups depGraph

        prettyBindGroup (expls, implss) = (pExpls, pImplss)
            where
                prettyExpl (x :>: _, _) = x ++ "*"
                prettyImpl (x, _) = x

                pExpls = map prettyExpl expls
                pImplss = map (map prettyImpl) implss



-- TYPECHECK EQN SEQ
----------------------------------------


-- show lemmas

caseThy = "test-data/pos/easy/cthy"
casePrf = "test-data/pos/easy/cprf"

showLemmas thy prf = do
    cthy <- readFile thy
    cprf <- readFile prf
    return $ showLemmas' cthy cprf

showLemmas' cthy cprf = do
    env <- processMasterFile "thy" cthy
    lemmas <- processProofFile env "prf" cprf
    return lemmas

-- TYPECHECK PROOF
----------------------------------------

equationThy = "test-data/no_unit/tc-proof/equation/cthy"
equationPrf = "test-data/no_unit/tc-proof/equation/cprf"

extCasesThy = "test-data/no_unit/tc-proof/ext-cases/cthy"
extCasesPrf = "test-data/no_unit/tc-proof/ext-cases/cprf"

inductionThy = "test-data/no_unit/tc-proof/induction/cthy"
inductionPrf = "test-data/no_unit/tc-proof/induction/cprf"
 

tcProofTest thy prf = do
    cthy <- readFile thy
    cprf <- readFile prf
    return $ tcProofTest' cthy cprf

tcProofTest' cthy cprf = do
    env <- processMasterFile "thy" cthy
    lemmas <- processProofFile env "prf" cprf
    as <- getTheoryAssumps env

    mapM_ (\l -> runProofTC as $ typeCheckLemma l) lemmas
    



-- TEST BLUEPRINT
----------------------------------------

natThyBP = "test-data/no_unit/blueprint/nat-add/bpthy"
natThy = "test-data/no_unit/blueprint/nat-add/cthy"
natPrfBP = "test-data/no_unit/blueprint/nat-add/bpprf"
natPrf = "test-data/no_unit/blueprint/nat-add/cprf"

natParams = BlueprintParams
    { thyBP = natThyBP
    , thySol = natThy
    , prfBP = natPrfBP
    , prfSol = natPrf
    }

inductionParams = BlueprintParams
    { thyBP = "test-data/no_unit/blueprint/induction/bpthy"
    , thySol = "test-data/no_unit/blueprint/induction/cthy"
    , prfBP = "test-data/no_unit/blueprint/induction/bpprf"
    , prfSol = "test-data/no_unit/blueprint/induction/cprf"
    }


data BlueprintParams = BlueprintParams
    { thyBP :: String, thySol :: String
    , prfBP :: String, prfSol :: String
    }

bpThyTest bp thy = do
    bpthy <- readFile bp
    cthy <- readFile thy
    return $ matchBlueprintWithTheory bpthy cthy

bpPrfTest params = do
    bpthy <- readFile $ thyBP params
    cthy <- readFile $ thySol params
    bpprf <- readFile $ prfBP params
    cprf <- readFile $ prfSol params
    return $ parsePrfTest' bpthy cthy bpprf cprf

parsePrfTest rawBpThy rawThy rawBpPrf rawPrf = do
    bpthy <- readFile rawBpThy
    cthy <- readFile rawThy
    bpprf <- readFile rawBpPrf
    cprf <- readFile rawPrf
    return $ parsePrfTest' bpthy cthy bpprf cprf

parsePrfTest' bpThy thy bpPrf prf = do
    env <- processMasterFile "" thy
    matchBlueprintWithProof env bpPrf prf



-- EQN SEQ TEST
--------------------------------------------

eqnSeq = Step x r1 $ Step y r2 $ Single z
    where
        x = Free "x"
        y = Free "y"
        z = Free "z"
        r1 = "def r10"
        r2 = "def r2"

singleSeq = Single x
    where
        x = Free "x"

stepSeq = Step x r1 $ Single y
    where
        x = Free "x"
        y = Free "y"
        r1 = "def r1"


-- error context demo
errorContextDemo :: TI a
errorContextDemo =
    withErrorContext (context 0) $
        withErrorContext (context 1) $
            liftWithContexts $ throwE $ text "Error"
            where
                context :: Int -> Doc
                context n = hsep $ map text $ ["Context", show n]

-- *Main> fromLeft empty $ runTI $ errorContextDemo 
-- Context 0
--     Context 1
--         Error