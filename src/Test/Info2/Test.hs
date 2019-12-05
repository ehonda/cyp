{-# LANGUAGE FlexibleContexts #-}

import Control.Monad.State
import qualified Text.Parsec as Parsec
import Text.PrettyPrint.HughesPJ
import qualified Language.Haskell.Exts.Simple.Syntax as Exts
import qualified Language.Haskell.Exts.Simple.Parser as P

import Test.Info2.Cyp.Env
import Test.Info2.Cyp.Parser
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Typing.Theory
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
parseSymbols c = parseTransform c readSym

parseFuncsConsts c = parseTransform c $ \r -> do
    syms <- fmap (defaultConsts ++) $ readSym r
    readFunc syms r

parseFuncs c = do
    (fs, _, _) <- parseFuncsConsts c
    return fs

parseConsts c = do
    (_, cs, _) <- parseFuncsConsts c
    return cs

parseAxioms c = do
    (_, cs, _) <- parseFuncsConsts c
    parseTransform c $ readAxiom cs

parseGoals c = do
    (_, cs, _) <- parseFuncsConsts c
    parseTransform c $ readGoal cs

inspectTheory path f = do
    c <- readFile path
    case f c of
        Right nodes -> mapM_ print nodes
        Left err -> print err
    
thyParse path = do
    c <- readFile path
    case eitherToErr $ Parsec.parse cthyParser path c of
        Right nodes -> mapM_ print nodes
        Left err -> print err

envTheory path = do
    thy <- readFile path
    case processMasterFile "thy" thy of
        Right env -> print env
        Left err -> print err

getEnv path = do
    thy <- readFile path
    case processMasterFile "thy" thy of
        Right env -> return env
        Left _ -> return declEnv
    

-- Proof file inspection as in processProofFile
---------------------------------------------------------------

parseProof thy prf = do
    env <- processMasterFile "thy" thy
    processProofFile env "prf" prf

inspectProof pthy pprf = do
    thy <- readFile pthy
    prf <- readFile pprf
    case parseProof thy prf of
        Right ls -> mapM_ print ls


-- Inspect checkProof stuff
---------------------------------------------------------------

-- let (eqns, env') = runState (traverse (state . declareTerm) reqns) env
declareEqns _ ParseCheating _ = err $ text "Cheating"
declareEqns prop (ParseEquation reqns) env = do
    let (eqns, env') = runState (traverse (state . declareTerm) reqns) env
    return eqns
--declareEqns prop (ParseExt withRaw toShowRaw proof) = do


declEqns :: String -> Env -> Err (EqnSeqq Term)
declEqns prf env = do
    -- processProofFile
    lemmas <- eitherToErr $ Parsec.runParser cprfParser env "" prf
    -- checkProofs
    case lemmas of
        [] -> return $ EqnSeqq (Single (Const "Err")) Nothing
        (l@(ParseLemma name rprop proof) : ls) -> do
            -- checkLemma
            let (prop, env') = declareProp rprop env
            -- checkProof
            declareEqns prop proof env'

-- rewrite stuff
--rewriteEqns prf env = do
--    let t1 = Application (Application (Const ":") (Free ("z",0))) (Free ("zs",0))
--    return $ rewrite t1 $ ((axioms env) !! 0)

testRe1 =
    let t = Free ("z", 0)
    in case rewriteTop t (Prop t t) of
        Just t' -> print t'
        Nothing -> print "rewrite failed"

--testRe2 =
--    let lhs = Application (Application (Const "+") (Literal (Int () 0 "0"))) (Schematic ("b",0))
--        rhs = Schematic ("b",0)
--    in case rewriteTop lhs (Prop lhs rhs) of
--        Just t' -> print t'
--        Nothing -> print "rewrite failed"
        

--tiSeq :: String -> Env -> Err [TI Type]
--tiSeq prf env = do
--    eqns <- declEqns prf env
--    

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






-- TESTING STUFF IN OTHER MODULES
-----------------------------------------------

-- validConsCaseTyped, Cyp.hs
-------------------------------------
termListCons = Application 
    (Application (Const "Cons") (Free ("x", 0))) 
    (Free ("xs", 0))

testValidCCase t decl = do
    dt <- testConv decl
    validConsCase t dt

testFuncDecomp decl = do
    dt <- testConv decl
    --  decompDCons :: [([Type], Type)]
    let decompDCons = map (decomposeFuncType . snd) $ dtConss dt
        prettyDecomps = map 
            (\(args, ret) -> (map prettyType args, prettyType ret))
            decompDCons
    return prettyDecomps

tiRunAndShowSub ti = runTI $ (ti >> getSubst)

--tiRunAndSub ti = runTI $ getSubst >>= \s -> apply s ti

tiRunAndSub ti = runTI $ do
    ti' <- ti
    s <- getSubst
    return $ apply s ti'

--tiRunAndPretty ti = prettyType $ tiRunAndSub ti

-- Read type bool and then infer type for read function
testDtAndFunBool = do
    dt <- fmap head $ readDataType [DataDecl "Bool = False | True"]
    let consAssumps = map consToAssump $ dtConss dt
        pCons = map (\a -> PCon a []) consAssumps
        alts = map (\p@(PCon (name :>: _) _) -> ([p], Const name)) pCons
        
    return $ mapM (tiAlt consAssumps) alts
--    return dt
    where
--        consToScheme (name, t) = name :>: toScheme t
        consToAssump (name, t) = name :>: quantify (tv t) t

--testFunPretty = fmap (map prettyType) $ fmap tiRunAndSub testDtAndFunBool


-- TEST INFER FUNCTION TYPES
----------------------------------------------------------------

defF = FunDef "f x = x"
--defG = FunDef "g (x:xs) = x"
defH = FunDef "h x y = x y"
defNot1 = FunDef "not False = True"
defNot2 = FunDef "not True = False"
defNotInv = FunDef "not (x:xs) = x"     -- NON EXHAUSTIVE PATTERNS
defNotX = FunDef "not X = X"

dtBool = DataType 
    { dtName = "Bool"
    , dtConss = [("False", tBool), ("True", tBool)]
    }
    where tBool = TCon (Tycon "Bool" Star)

dtX = DataType {dtName = "X", dtConss = [("X", tX)]}
    where tX = TCon (Tycon "X" Star)

testDts = defaultDataTypes ++ [dtBool, dtX]


-- TEST THEORY TYPE CHECK
--------------------------------------------

testTypeCheckTheory path = do
    env <- getEnv path
    case typeCheckTheory env of
        Right tti -> printTheoryTypeInfo tti
        Left e -> print e



-- TEST UNIT TEST STUFF
--------------------------------------------

--negConsArgs = "test-data/neg/wrong-conspat-arg-num/"
--negOtherGoal = "test-data/neg/other-goal/"
--
--testNegUnit path = do
--    expFail <- readFile $ path ++ "cout"
--    cthy <- readFile $ path ++ "cthy"
--    cprf <- readFile $ path ++ "cprf"
--
--    return $ testNegUnit' expFail cthy cprf
--
--
--testNegUnit' expFail cthy cprf = do
--    case proof ("thy", cthy) ("prf", cprf) of
--        Left e -> expFail : [render e]
--        _ -> []




-- TEST TYPECHECK FUNCTION ALTS
--------------------------------------------

tcFunEasy = "test-data/no_unit/tc-fun/easy/cthy"
tcFunConPatPoly = "test-data/no_unit/tc-fun/conpat-on-poly-fun/cthy"
tcFunDouble = "test-data/no_unit/tc-fun/double/cthy"

testTCFunctionAlts path = do
    env <- getEnv path
    return $ runTI $ typeCheckFunctionsAlts env

prettyIOAssumps :: IO (Err [Assump]) -> IO (Err [String])
prettyIOAssumps = fmap (fmap (map prettyAssump))

-- TI EXPL BINDING
----------------------------------------
testExplBinding path = do
    env <- getEnv path
    return $ testExplBinding' env

testExplBinding' env = runTI $ 
    mapM (tiExplBind as) expls
    where
        funAlts = functionsAlts env
        typeSigs = typeSignatures env
        as = getConsAssumptions $ datatypes env

        expls = zip typeSigs $ map snd funAlts

-- TI IMPL BINDING
----------------------------------------
testImplBinding path = do
    env <- getEnv path
    return $ testImplBinding' env

testImplBinding' env = runTI $ 
    tiImplBinds as impls
    where
        --tv = TVar $ Tyvar "a" Star
        --sigD = "d" :>: quantifyAll (tv `fn` tv)
        as = sigD : (getConsAssumptions $ datatypes env)


        impls = functionsAlts env