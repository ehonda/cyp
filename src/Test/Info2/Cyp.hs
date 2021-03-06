{-# LANGUAGE FlexibleContexts #-}

-- module Test.Info2.Cyp (
--   proof
-- , proofFile
-- ) where

module Test.Info2.Cyp where

import Prelude hiding ((<>))
import Control.Monad
import Control.Monad.State
import Data.Foldable (for_)
import Data.List
import qualified Data.Map.Strict as M
import Data.Maybe
import qualified Text.Parsec as Parsec
import Text.PrettyPrint (colon, comma, empty, fsep, int, punctuate, hsep, quotes, text, vcat, (<>), (<+>), ($+$))

import Test.Info2.Cyp.Blueprint.Blueprint
import Test.Info2.Cyp.Env
import Test.Info2.Cyp.Parser
import Test.Info2.Cyp.Proof
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Typing.Inference
import Test.Info2.Cyp.Typing.Proof
import Test.Info2.Cyp.Typing.Theory
import Test.Info2.Cyp.Util

proofFile :: FilePath -> FilePath -> IO (Err ())
proofFile masterFile studentFile = do
    mContent <- readFile masterFile
    sContent <- readFile studentFile
    return $ proof (masterFile, mContent) (studentFile, sContent)

proofFileBlueprint :: FilePath 
    -> FilePath 
    -> Maybe FilePath   -- BP Proof does not have to be supplied 
    -> FilePath 
    -> IO (Err ())
proofFileBlueprint bpThyFile solThyFile bpPrfFile solPrfFile = do
    bpThy <- readFile bpThyFile
    solThy <- readFile solThyFile
    bpPrf <- maybe (return Nothing) 
        (\bp -> do c <- readFile bp; return $ Just c) bpPrfFile
    solPrf <- readFile solPrfFile
    return $ proofBlueprint bpThy solThy bpPrf solPrf

typeCheckTheoryFile :: FilePath -> IO (Err TheoryTypeInfo)
typeCheckTheoryFile path = do
    thy <- readFile path
    return $ tcTheory path thy

tcTheory :: FilePath -> String -> Err TheoryTypeInfo
tcTheory path content = do
    env <- processMasterFile path content
    typeCheckTheory env

proof :: (String, String) -> (String, String) -> Err ()
proof (mName, mContent) (sName, sContent) = do
    env <- processMasterFile mName mContent
    typeCheckTheory env
    
    lemmaStmts <- processProofFile env sName sContent
    results <- checkProofs env lemmaStmts
    case filter (not . contained results) $ goals env of
        [] -> return ()
        xs -> err $ indent (text "The following goals are still open:") $
            vcat $ map unparseProp xs
  where
    contained props goal = any (\x -> isJust $ matchProp goal (namedVal x) []) props

-- TODO: thy file is read multiple times here, could be done better
proofBlueprint :: String -> String -> Maybe String -> String -> Err ()
proofBlueprint bpThy solThy bpPrf solPrf = do
    matchBlueprintWithTheory bpThy solThy
    env <- processMasterFile "Solution Theory" solThy
    maybe noAction (\bp -> matchBlueprintWithProof env bp solPrf) bpPrf
    proof ("Solution Theory", solThy) ("Solution Proof", solPrf)
    where
        noAction = return ()

processMasterFile :: FilePath -> String -> Err Env
processMasterFile path content = errCtxtStr "Parsing background theory" $ do
    mResult <- eitherToErr $ Parsec.parse cthyParser path content
    -- Datatypes
    dts <- fmap (++ defaultDataTypes) $ readDataType mResult
    let consAs = getConsAssumptions dts

    -- Read user type signatures
    typeSigs <- readTypeSigs mResult
    -- Check for duplicate type sigs
    let sigGroups = groupBy
            (\a a' -> assumpName a == assumpName a')
            typeSigs

        checkGroup :: [Assump] -> Err ()
        checkGroup g = unless (length g == 1) $
            errCtxtStr "Duplicate type signatures:" $
                err $ vcat $ map assumpDoc g
    mapM_ checkGroup sigGroups

    -- Functions
    -- TODO: This should be done cleaner. Need to add type
    --       sigs so abstract functions are recognized as such
    --       when used in the definition of a concrete function
    --
    --      also the kind of same thing is done further down,
    --      with abstractFunsNames and consts' -> REFACTOR
    let rfConsts = defaultConsts ++ (map assumpName typeSigs)
    (fundefs, consts, funsRawAlts) <- readFunc rfConsts mResult
    funsAlts <- traverse (convertFunctionRawAlts consAs) funsRawAlts

    -- Bindings
    let definedFunsNames = map fst funsAlts
        abstractFunsNames = map assumpName $ filter 
            (\(f :>: _) -> f `notElem` definedFunsNames)
            typeSigs

        funsAlts' = funsAlts ++ (map (\f -> (f, [])) abstractFunsNames)
        (expls, impls) = toBindings funsAlts' typeSigs
        -- Add type sigs to consts to support
        -- declaring a function without providing
        -- an implementation
        consts' = nub $ consts ++ (map assumpName typeSigs)
    
    -- Axioms and Goals
    axs <- readAxiom consts' mResult
    gls <- readGoal consts' mResult

    return $ Env 
        { datatypes = dts
        , explicitBindings = expls
        , implicitBindings = impls
        , axioms = fundefs ++ axs
        , constants = consts'
        , fixes = M.empty
        , goals = gls 
        }

processProofFile :: Env -> FilePath -> String -> Err [ParseLemma]
processProofFile env path content = errCtxtStr "Parsing proof" $
    eitherToErr $ Parsec.runParser cprfParser env path content

checkProofs :: Env -> [ParseLemma] -> Err [Named Prop]
checkProofs env []  = Right $ axioms env
checkProofs env (l : ls) = do
    (_, env') <- checkLemma l env
    checkProofs env' ls

checkLemma :: ParseLemma -> Env -> Err (Prop, Env)
checkLemma lem@(ParseLemma name rprop proof) env = errCtxt (text "Lemma" <+> text name <> colon <+> unparseRawProp rprop) $ do
    -- Typecheck the lemma
    as <- getTheoryAssumps env
    errCtxt (text "While typechecking the proof") $
        runProofTC as $ typeCheckLemma lem

    let (prop, env') = declareProp rprop env
    Prop _ _ <- checkProof prop proof env'
    let proved = generalizeEnvProp env prop
    return (proved, env { axioms = Named name proved : axioms env })

checkProof :: Prop -> ParseProof -> Env -> Err Prop
checkProof prop (ParseEquation reqns) env = errCtxtStr "Equational proof" $ do
--    let (eqns, env') = runState (traverse (state . declareTerm) reqns) env
    let (eqns, env') = toInterpretedEqns reqns env
    proved <- validEqnSeqq (axioms env') eqns
    when (prop /= proved) $ err $
        text "Proved proposition does not match goal:" `indent` unparseProp proved
    return proved
checkProof prop (ParseExt sig@(withId :>: _) toShowRaw proof) env = errCtxt ctxtMsg $
    flip evalStateT env $ do
        with <- validateWith $ Free withId
        prop' <- validateShow with toShowRaw
        env <- get
        lift $ checkProof prop' proof env
  where
    ctxtMsg = text "Extensionality with" <+> text (prettyAssump' sig)

    validateWith t = do -- lazy code duplication
        t' <- state (declareTerm t)
        case t' of
            Free v -> return v
            _ -> lift $ err $ text "Term" <+> quotes (unparseTerm t')
                <+> text "is not a valid variable for extensionality"

    validateShow v raw = do
        prop' <- state (declareProp raw)
        let Prop lhs rhs = prop
        let Prop lhs' rhs' = prop'
        let lhsE = Application lhs (Free v)
        let rhsE = Application rhs (Free v)
        when (lhsE /= lhs') $ bail "Invalid left-hand side of proposition, expected:" lhsE
        when (rhsE /= rhs') $ bail "Invalid right-hand side of proposition, expected:" rhsE
        return prop'
      where
        bail msg t = lift $ err $ text msg <+> quotes (unparseTerm t)
checkProof prop (ParseInduction typeSig@(overId :>: dtSc) gens casesRaw) env = errCtxt ctxtMsg $ do
    dt <- validDatatypeFromScheme dtSc env
    flip evalStateT env $ do
        over <- validateVar "induction" $ Free overId
        gens <- traverse (validateVar "generalization") gensRaw
        env <- get
        validateGens over gens prop
        lift $ validateCases dt over gens casesRaw env
        return prop
  where
    ctxtMsg = text "Induction over variable"
        <+> (text $ prettyAssump' typeSig)
        <+> if null gensRaw then empty else text "generalizing over" <+> fsep (map (quotes . unparseRawTerm) gensRaw)

    gensRaw = map (Free . assumpName) gens

    unparseVarList vars = fsep (intersperse (text ",") (map (unparseTerm . Free) vars))
    unparseGenProp gens prop =
        (if null gens then empty else text "forall" <+> unparseVarList gens <+> text ":") <+> unparseProp prop

    checkGenNum lv lg = do
        when (lv < lg) $ err $ text "Not enough variables universally quantified:" <+> int lv <+> text "out of" <+> int lg
        when (lv > lg) $ err $ text "Too many variables universally quantified:" <+> int lv <+> text "instead of" <+> int lg

    validateVar s t = do
        t' <- state (declareTerm t)
        case t' of
            Free v -> return v
            _ -> lift $ err $ text "Term" <+> quotes (unparseTerm t')
                <+> text ("is not a valid " ++ s ++ " variable")

    validateGens over gens prop =
       if over `elem` gens then lift $ err $
           text "Cannot generalize induction variable" <+> quotes (unparseTerm (Free over))
       else case find (\x -> not (x `elem` frees)) gens of
           Nothing -> return ()
           Just v -> lift $ err $
               text "Cannot generalize variable" <+> quotes (unparseTerm (Free v)) <+>
               text "that does not occur in the goal"
       where
         frees = delete over (collectFreesProp prop [])

    validateCases dt over gens cases env = 
        validateCasesWith (validateCase dt over gens env) dt cases 

    validateCase dt over gens env pc = errCtxt 
      (text "Case" <+> quotes (unparseRawTerm $ pcCons pc) <+>
        (case pcFixs pc of
           Nothing -> empty
           Just as -> text "Fixing" <+> hsep (map (quotes . text . prettyAssump') as)) <+>

        case pcGens pc of
           Nothing -> empty
           --Just rawVars -> text "For arbitrary" <+> hsep (map (quotes . unparseRawTerm) rawVars))
           Just as -> text "For arbitrary" <+> hsep (map (quotes . text . prettyAssump') as))
      $ do flip evalStateT env $ do
            caseT <- state (variantFixesTerm $ pcCons pc)
            (consName, consArgNs) <- lift $ validConsCase caseT dt
            let recArgNames = map snd $ filter (\x -> fst x == TRec) consArgNs

            let subgoal = substFreeProp prop [(over, caseT)]

            case pcFixs pc of
                Nothing -> when (not $ null recArgNames) $ lift $ err $ text "Missing 'Fix {constructor arguments...}'"
                Just as -> do
                    let conNs = map (Free . fst . snd) consArgNs
                        rawVars = map (Free . assumpName) as
                    when (sort rawVars /= sort conNs) $ lift . err
                        $ text "Fixed variables do not match with the Case"

            case pcGens pc of
                Nothing -> when (not $ null gens) $ lift $ err $ text "Missing 'For fixed ...'"
                Just as -> do
                    vars <- traverse (validateVar "generalization") rawVars
                    when (vars /= gens) $ lift . err
                         $ text "Variable names do not match"
                         `indent` (text "Generalization variables:" <+> fsep (intersperse (text ",") (map (unparseTerm . Free) gens))
                         $+$ text "'fixed' variables:" <+> fsep (intersperse (text ",") (map (unparseTerm . Free) vars)))
                    where
                        rawVars = map (Free . assumpName) as

            case pcToShow pc of
                Nothing ->
                    lift $ err $ text "Missing 'Show'"
                Just raw -> do
                    toShow <- state (declareProp raw)
                    when (subgoal /= toShow) $ lift . err
                         $ text "'Show' does not match subgoal:"
                         `indent` (
                            text "Show:" <+> unparseGenProp gens toShow
                            $+$ debug (text "Subgoal:" <+> unparseGenProp gens subgoal))

                    userHyps <- checkPcHyps over gens recArgNames $
                        map toOldAssm $ pcAssms pc

                    modify (\env -> env { axioms = userHyps ++ axioms env })
                    env <- get
                    Prop _ _ <- lift $ checkProof subgoal (pcProof pc) env
                    return consName

    checkPcHyps over gens recVars rpcHyps = do
        pcHyps <- traverse (traverse (\(rawVars, raw) -> do
            vars <- traverse (validateVar "generalization") rawVars
            prop <- state (declareProp raw)
            lift $ checkGenNum (length rawVars) (length gens)
            validateGens over vars prop
            return $ substFreeProp prop (zip vars (map Free gens)))) rpcHyps
        let indHyps = map (substFreeProp prop . instOver) recVars
        lift $ for_ pcHyps $ \(Named name prop) -> case prop `elem` indHyps of
            True -> return ()
            False -> err $
                text ("Induction hypothesis " ++ name ++ " is not valid") `indent` (unparseGenProp gens prop)
        return $ fmap (fmap (generalizeOnlyProp gens)) pcHyps
      where
        instOver n = [(over, Free n)]
checkProof prop (ParseCases dtSc onRaw casesRaw) env = errCtxt ctxtMsg $ do
    dt <- validDatatypeFromScheme dtSc env
    flip evalStateT env $ do
        on <- state (declareTerm onRaw)
        env <- get
        lift $ validateCases dt on casesRaw env
        return prop
  where
    ctxtMsg = text "Case analyis on" <+> quotes (unparseRawTerm onRaw) 
        <+> text "of type" <+> quotes (text $ prettyScheme dtSc)

    validateCases dt on cases env = 
        validateCasesWith (validateCase dt on env) dt cases 

    validateCase dt on env pc = errCtxt (text "Case" <+> quotes (unparseRawTerm $ pcCons pc)) $ do
        flip evalStateT env $ do
            caseT <- state (variantFixesTerm $ pcCons pc)
            (consName, _) <- lift $ validConsCase caseT dt

            when (isJust $ pcGens pc) $
                lift $ errStr "Superfluous 'For fixed'"

            when (isJust $ pcToShow pc) $
                lift $ errStr "Superfluous 'Show'"

            userAssm <- checkPcAssms on caseT $ map toOldAssm $ pcAssms pc

            modify (\env -> env { axioms = userAssm : axioms env })
            env <- get
            Prop _ _ <- lift $ checkProof prop (pcProof pc) env
            return consName

    checkPcAssms :: Term -> Term -> [Named ([RawTerm], RawProp)] -> StateT Env Err (Named Prop)
    checkPcAssms on caseT [Named name ([], rawProp)] = do
        prop <- state (declareProp rawProp)
        let Prop lhs rhs = prop
        when (lhs /= on) $ bail "Invalid left-hand side of assumption, expected:" on
        when (rhs /= caseT) $ bail "Invalid right-hand side of assumption, expected:" caseT
        return $ Named name prop
      where
        bail msg t = lift $ err $ text msg <+> quotes (unparseTerm t)
    checkPcAssms _ _ [_] = lift $ errStr "No generalization in a case distinction"
    checkPcAssms _ _ _ = lift $ errStr "Expected exactly one assumption"


-- Helper functions for ParseInduction, ParseCases
toOldAssm :: Named ([Assump], RawProp) -> Named ([RawTerm], RawProp)
toOldAssm (Named name (genAs, prop)) = Named name (gens, prop)
    where
        gens = map (Free . assumpName) genAs 

validateCasesWith validateCase dt cases = do
    caseNames <- traverse validateCase cases
    case missingCase caseNames of
        Nothing -> return ()
        Just (name :>: _) -> errStr $ "Missing case '" ++ name ++ "'"
  where
      missingCase caseNames = find (\a -> (assumpName a) `notElem` caseNames) (dtConss dt)

validDatatypeFromScheme :: Scheme -> Env -> Err DataType
validDatatypeFromScheme sc env = case 
    find (\dt -> schemeInstsAreUnifiable sc $ dtScheme dt) (datatypes env) of
        Nothing -> err $ fsep $
            [ text "Invalid datatype" <+> quotes (text $ prettyScheme sc) <> text "."
            , text "Expected one of:" ]
            ++ punctuate comma (map (quotes . text . prettyScheme . dtScheme) $ datatypes env)
        Just dt -> Right dt

validConsCase :: Term -> DataType -> Err (String, [(TConsArg, IdxName)])
validConsCase t (DataType _ dcons) = errCtxt invCaseMsg $ do
    consName :>: consScheme <- findCons cons
    consType <- runTI $ freshInst consScheme
    let (_, consArgs) = toOldDataConstructor (consName, consType)
    
    argNames <- traverse argName args
    when (not $ nub args == args) $
        errStr "Constructor arguments must be distinct"
    when (not $ length args == length consArgs) $
        errStr "Invalid number of arguments"
    return (consName, zip consArgs argNames)
    where
        (cons, args) = stripComb t

        argName (Free v) = return v
        argName _ = errStr "Constructor arguments must be variables"

        findCons (Const name) = case find (\c -> assumpName c == name) dcons of
            Nothing -> err (text "Invalid constructor, expected one of"
                <+> (fsep . punctuate comma . map (quotes . text . prettyAssump') $ dcons))
            Just x -> return x
        findCons _ = errStr "Outermost symbol is not a constant"

        invCaseMsg = text "Invalid case" <+> quotes (unparseTerm t) <> comma

validEqnSeq :: [Named Prop] -> EqnSeq Term -> Err Prop
validEqnSeq _ (Single t) = return (Prop t t)
validEqnSeq rules (Step t1 rule es)
    | rewritesToWith rule rules t1 t2 = do
        Prop _ tLast <- validEqnSeq rules es
        return (Prop t1 tLast)
    | otherwise = errCtxtStr ("Invalid proof step" ++ noRuleMsg) $ err $
        unparseTerm t1 $+$ text ("(by " ++ rule ++ ") " ++ symPropEq) <+> unparseTerm t2
        $+$ debug (text rule <> text ":" <+> vcat (map (unparseProp . namedVal) $ filter (\x -> namedName x == rule) rules))
  where
    (t2, _) = eqnSeqEnds es
    noRuleMsg
        | any (\x -> namedName x == rule) rules = ""
        | otherwise = " (no rules with name \"" ++ rule ++ "\")"

validEqnSeqq :: [Named Prop] -> EqnSeqq Term -> Err Prop
validEqnSeqq rules (EqnSeqq es1 Nothing) = validEqnSeq rules es1
validEqnSeqq rules (EqnSeqq es1 (Just es2)) = do
    Prop th1 tl1 <- validEqnSeq rules es1
    Prop th2 tl2 <- validEqnSeq rules es2
    case tl1 == tl2 of
        True -> return (Prop th1 th2)
        False -> errCtxtStr "Two equation chains don't fit together:" $
            err $ unparseTerm tl1 $+$ text symPropEq $+$ unparseTerm tl2

rewriteTop :: Term -> Prop -> Maybe Term
rewriteTop t (Prop lhs rhs) = fmap (subst rhs) $ match t lhs []

rewrite :: Term -> Prop -> [Term]
rewrite t@(Application f a) prop =
    maybeToList (rewriteTop t prop)
    ++ map (\x -> Application x a) (rewrite f prop)
    ++ map (Application f) (rewrite a prop)
rewrite t prop = maybeToList $ rewriteTop t prop

rewritesTo :: [Prop] -> Term -> Term -> Bool
rewritesTo rules l r = l == r || rewrites l r || rewrites r l
  where rewrites from to = any (\x -> isJust $ match to x []) $ concatMap (rewrite from) rules

rewritesToWith :: String -> [Named Prop] -> Term -> Term -> Bool
rewritesToWith name rules l r = rewritesTo (f rules) l r
  where f = map namedVal . filter (\x -> namedName x == name)
