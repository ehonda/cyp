import Control.Monad.State
import qualified Text.Parsec as Parsec
import Text.PrettyPrint.HughesPJ
import qualified Language.Haskell.Exts.Simple.Syntax as Exts

import Test.Info2.Cyp.Env
import Test.Info2.Cyp.Parser
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Util
import Test.Info2.Cyp

trivThy = "test-data/pos/trivial/cthy"
trivPrf = "test-data/pos/trivial/cprf"

revThy = "test-data/pos/revrev/cthy"
revPrf = "test-data/pos/revrev/cprf"

lenThy = "test-data/pos/length-append/cthy"
lenPrf = "test-data/pos/length-append/cprf"

wcThy = "test-data/no_unit/wildcard/cthy"

cthy base = base ++ "cthy"
cprf base = base ++ "cprf"

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
    (fs, _) <- parseFuncsConsts c
    return fs

parseConsts c = do
    (_, cs) <- parseFuncsConsts c
    return cs

parseAxioms c = do
    (_, cs) <- parseFuncsConsts c
    parseTransform c $ readAxiom cs

parseGoals c = do
    (_, cs) <- parseFuncsConsts c
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
