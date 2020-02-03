module Test.Info2.Cyp.Blueprint.Blueprint where

import Control.Monad
import Data.List
import Data.Maybe
import qualified Text.Parsec as Parsec

import Test.Info2.Cyp.Parser
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Typing.Inference -- ONLY FOR capIndent etc
import Test.Info2.Cyp.Util

import Text.PrettyPrint

hole :: RawTerm
hole = Const symHole

isHole :: RawTerm -> Bool
isHole term
    | term == hole = True
    | otherwise = False

hasHole :: RawTerm -> Bool
hasHole (Application a b) = (hasHole a) || (hasHole b)
hasHole term = isHole term

-- Utility functions to compare blueprint with solution
-------------------------------------------------------
comparisonDoc :: String -> (a -> Doc) -> a -> a -> Doc
comparisonDoc header toDoc blueprint solution =
    capIndent
        header
        [ capIndent "Blueprint:" [toDoc blueprint]
        , capIndent "Solution:" [toDoc solution]
        ]


toRawTerm :: Term -> RawTerm
toRawTerm (Application a b) = 
    Application (toRawTerm a) (toRawTerm b)
toRawTerm (Const c) = Const c
toRawTerm (Free (x, _)) = Free x
toRawTerm (Schematic (x, _)) = Schematic x
toRawTerm (Literal l) = Literal l

matchBlueprintWithTerm :: Term -> Term -> Err ()
matchBlueprintWithTerm bp term =
    matchBlueprintWithRawTerm (toRawTerm bp) (toRawTerm term)

-- first argument is blueprint, second the term with
-- all holes filled out
matchBlueprintWithRawTerm :: RawTerm -> RawTerm -> Err ()
matchBlueprintWithRawTerm bp term = do
    -- First check that term to match with contains no holes
    when (hasHole term) $
        err $ hsep
            [ text $ "Term"
            , quotes $ unparseRawTerm term
            , text $ "to match with should not contain holes."
            ]

    match bp term
    where
        match :: RawTerm -> RawTerm -> Err ()
        -- Hole
        match bp _ 
            | bp == hole = return ()
        
        -- Application
        match (Application a b) (Application a' b') = do
            match a a'
            match b b'

        -- Rest
        match bp term
            | bp == term = return ()
            | otherwise = err $ comparisonDoc 
                "Term mismatch:"
                unparseRawTermPretty
                bp term

-- Utility to compare the various lists
---------------------------------------------------------
compareMaybes :: String
    -> (a -> a -> Err ()) 
    -> Maybe a -> Maybe a -> Err ()
compareMaybes _ cmpAction (Just bp) (Just sol) =
    cmpAction bp sol
compareMaybes _ _ Nothing Nothing =
    return ()
compareMaybes property  _ bp _ = err errMsg
    where
        errMsg :: Doc
        errMsg = hsep $ map text
            [ has, "has", property
            , "but", hasnt, "hasn't."
            ]

        (has, hasnt) = if isJust bp 
            then ("Blueprint", "Solution")
            else ("Solution", "Blueprint")


compareEq :: Eq a => String 
    -> (a -> Doc)
    -> a -> a -> Err ()
compareEq header toDoc blueprint solution = 
    when (blueprint /= solution) $ err $ 
        comparisonDoc header toDoc blueprint solution

compareMany :: String
    -> (a -> a -> Err ())
    -> [a] -> [a] -> Err ()
compareMany msgLenMismatch cmpAction bps sols = do
    when (length bps /= length sols) $ err $
        hcat $ map text $
            [ msgLenMismatch
            , " Blueprint has "
            , show $ length bps
            , ", Solution has "
            , show $ length sols
            , "."
            ]
    zipWithM_ cmpAction bps sols


-- Match theories
--------------------------------------------------------

matchBlueprintWithTheory :: String -> String -> Err ()
matchBlueprintWithTheory blueprint theory = 
    errCtxtStr "While matching blueprint theory with solution theory" $ do
        (bpDts, bpSigs, bpFuns, bpAxs, bpGls) <-
            getTheoryContents readFuncBlueprint blueprint "Parsing blueprint"
        (thyDts, thySigs, thyFuns, thyAxs, thyGls) <-
            getTheoryContents readFunc theory "Parsing solution"

        compareDataTypes bpDts thyDts
        compareTypeSignatures bpSigs thySigs
        matchFunctions bpFuns thyFuns
        compareAxioms bpAxs thyAxs
        compareGoals bpGls thyGls
        where
            -- Duplication from Cyp.hs, refactor!
            getTheoryContents readFunc thy context = errCtxtStr context $ do
                res <- eitherToErr $ Parsec.parse cthyParser "" thy
                dts <- fmap (++ defaultDataTypes) $ readDataType res
                sigs <- readTypeSigs res
                syms <- fmap (defaultConsts ++) $ readSym res
                (_, consts, funsRawAlts) <- readFunc syms res
                let consAs = getConsAssumptions dts
                funsAlts <- traverse (convertFunctionRawAlts consAs) funsRawAlts
                axs <- readAxiom consts res
                gls <- readGoal consts res
                return (dts \\ defaultDataTypes, sigs, funsAlts, axs, gls)

            compareDataTypes :: [DataType] -> [DataType] -> Err ()
            compareDataTypes bps sols = compareMany
                "Number of datatypes doesn't match."
                (compareEq "Datatype mismatch:" dataTypeDoc)
                bps sols

            compareTypeSignatures :: [Assump] -> [Assump] -> Err ()
            compareTypeSignatures bps sols = compareMany
                "Number of type signatures doesn't match."
                (compareEq "Type signature mismatch:" assumpDoc)
                bps sols

            compareAxioms :: [Named Prop] -> [Named Prop] -> Err ()
            compareAxioms bps sols = compareMany
                "Number of axioms doesn't match."
                (compareEq "Axiom mismatch:" axiomDoc)
                bps sols
                where
                    axiomDoc (Named n a) = (text $ n ++ ":") <+>
                        unparsePropPretty a

            compareGoals :: [Prop] -> [Prop] -> Err ()
            compareGoals bps sols = compareMany
                "Number of goals doesn't match."
                (compareEq "Goal mismatch:" unparsePropPretty)
                bps sols

            -- Utility to compare/match the functions which can
            -- contain holes
            ---------------------------------------------------------
            matchAlt :: Alt -> Alt -> Err ()
            matchAlt (bpLhs, bpRhs) (solLhs, solRhs) = do
                compareEq "Left-hand side mismatch" lhsDoc bpLhs solLhs
                errCtxtStr "Right-hand side mismatch" $ 
                    matchBlueprintWithTerm bpRhs solRhs
                where
                    lhsDoc lhs = hsep $ map (text . prettyPat) lhs

            matchFunctions :: [FunctionAlts] 
                -> [FunctionAlts] -> Err ()
            matchFunctions bps sols = compareMany
                "Number of function declarations doesn't match."
                matchFuncs
                bps sols
                where
                    matchFuncs :: FunctionAlts 
                        -> FunctionAlts -> Err ()
                    matchFuncs (f, fAlts) (g, gAlts) = do
                        compareEq "Function name mismatch:" text f g
                        errCtxt errContext $ compareMany
                            "Number of function alternatives doesn't match."
                            matchAlt
                            fAlts gAlts
                        where
                            funAltsListDoc = vcat
                                [ capIndent
                                    ("Blueprint " ++ f ++ " alternatives:") $
                                    map (altDocWithName f) fAlts
                                , capIndent
                                    ("Solution " ++ g ++ " alternatives:") $
                                    map (altDocWithName g) gAlts
                                ]

                            errContext = capIndent
                                "While matching the following functions:"
                                [funAltsListDoc]

-- Match proofs
--------------------------------------------------------

-- Utility used by match proof
-----------------------------------
eqnSeqDoc :: (a -> Doc) -> EqnSeq a -> Doc
eqnSeqDoc toDoc seq = vcat
    [ nest 4 $ toDoc start
    , text ".=. ..."
    , text ".=." <+> toDoc end
    ]
    where
        (start, end) = eqnSeqEnds seq

eqnSeqRawTermDoc :: EqnSeq RawTerm -> Doc
eqnSeqRawTermDoc = eqnSeqDoc unparseRawTermPretty

matchEqnSeqqs :: EqnSeqq RawTerm -> EqnSeqq RawTerm -> Err ()
matchEqnSeqqs (EqnSeqq bpS bpT) (EqnSeqq solS solT) = do
    matchEqnSeqs bpS solS
    compareMaybes 
        "inverse equation sequence"
        matchEqnSeqs
        bpT solT
        

matchEqnSeqs :: EqnSeq RawTerm -> EqnSeq RawTerm -> Err ()
matchEqnSeqs (Single bpTerm) (Single solTerm) = 
    matchBlueprintWithRawTerm bpTerm solTerm
matchEqnSeqs bp@(Step bpTerm bpRule bpSeq) 
    sol@(Step solTerm solRule solSeq) = errCtxt context $ do
        matchBlueprintWithRawTerm bpTerm solTerm
        matchRules bpRule solRule
        matchEqnSeqs bpSeq solSeq
        where
            context = comparisonDoc
                "While matching the equation sequences:"
                eqnSeqRawTermDoc
                bp sol

            matchRules :: String -> String -> Err ()
            matchRules bp sol = unless (isRuleHole bp) $
                compareEq "Rule mismatch:" text bp sol
                where
                    isRuleHole :: String -> Bool
                    isRuleHole "_" = True
                    isRuleHole _ = False

-- Single and step match
-- TODO: BETTER ERROR MESSAGE
matchEqnSeqs _ _ = errStr "Equation sequence mismatch."


-- Match proof
-----------------------------------
matchBlueprintWithProof :: Env -> String -> String -> Err ()
matchBlueprintWithProof env blueprint solution = 
    errCtxtStr "While matching blueprint proof with solution proof" $ do
        bpLemmas <- getProofContents cprfParserBlueprint env blueprint
            "Parsing blueprint"
        solLemmas <- getProofContents cprfParser env solution
            "Parsing solution"
        compareMany
            "Number of lemmas doesn't match."
            matchLemmas
            bpLemmas solLemmas
        where
            getProofContents ::
                    Parsec.Parsec [Char] Env [ParseLemma]
                ->  Env
                ->  String
                ->  String
                ->  Err [ParseLemma]
            getProofContents proofParser env prf context =
                errCtxtStr context $ eitherToErr $ 
                    Parsec.runParser proofParser env "" prf

            matchLemmas :: ParseLemma -> ParseLemma -> Err ()
            matchLemmas 
                (ParseLemma bpName bpProp bpProof)
                (ParseLemma solName solProp solProof) = errCtxt context $ do
                    compareEq "Lemma name mismatch:" text
                        bpName solName
                    compareEq "Lemma proposition mismatch:" 
                        unparseRawPropPretty bpProp solProp
                    matchProofs bpProof solProof
                    where
                        lemmaDoc name prop = (text $ name ++ ":") <+>
                            (unparseRawPropPretty prop)
                        context = capIndent
                            "While matching lemmas"
                            [(text "Blueprint lemma") <+> (lemmaDoc bpName bpProp)]

            matchProofs :: ParseProof -> ParseProof -> Err ()
            -- INDUCTION
            matchProofs 
                (ParseInduction bpOver bpGens bpCases)
                (ParseInduction solOver solGens solCases) = errCtxt context $ do
                    compareEq "Induction variable mismatch:" 
                        assumpDoc bpOver solOver
                    compareMany
                        "Number of generalization variables doesn't match."
                        (compareEq "Generalization variable mismatch:" assumpDoc)
                        bpGens solGens
                    matchManyCases bpCases solCases
                    where
                        context = capIndent
                            "Blueprint Induction:"
                            [ text "Induction variable:" <+>
                                assumpDoc bpOver
                            , if null bpGens then empty else gensDoc
                            ]

                        gensDoc = hcat $ (text "Generalization variables:") :
                            (intersperse (text ", ") $
                                map assumpDoc bpGens)

            -- EQUATIONAL
            matchProofs
                (ParseEquation bpEqns) (ParseEquation solEqns) = 
                    errCtxtStr "While matching equational proofs" $
                        matchEqnSeqqs bpEqns solEqns

            -- EXTENSIONAL
            matchProofs
                (ParseExt bpWith bpToShow bpProof)
                (ParseExt solWith solToShow solProof) = errCtxt context $ do
                    compareEq "Extensionality variable mismatch:"
                        assumpDoc bpWith solWith
                    compareEq "'To show' mismatch:"
                        unparseRawPropPretty bpToShow solToShow
                    matchProofs bpProof solProof
                    where
                        context = capIndent
                            "Blueprint Extensionality:"
                            [ text "With variable:" <+>
                                assumpDoc bpWith
                            , text "To show:" <+>
                                unparseRawPropPretty bpToShow
                            ]

            -- CASES
            matchProofs
                (ParseCases bpScheme bpTerm bpCases)
                (ParseCases solScheme solTerm solCases) = errCtxt context $ do
                    compareEq "Case term type scheme mismatch:"
                        (text . prettyScheme) bpScheme solScheme
                    compareEq "Case term mismatch:"
                        unparseRawTermPretty bpTerm solTerm
                    matchManyCases bpCases solCases
                    where
                        context = capIndent
                            "Blueprint Case analysis:"
                            [ text "Over term:" <+>
                                unparseRawTermPretty bpTerm
                            , text "Term Scheme:" <+>
                                (text $ prettyScheme bpScheme)
                            ]

            -- PROOF TYPES MISMATCH
            matchProofs bp sol = err errMsg
                where
                    errMsg = hsep $ map text $
                        [ "Proof types don't match."
                        , "Blueprint is"
                        , (proofType bp) ++ ","
                        , "Solution is"
                        , (proofType sol) ++ "."
                        ]

                    proofType :: ParseProof -> String
                    proofType (ParseInduction _ _ _) = "Inductional proof"
                    proofType (ParseEquation _) = "Equational proof"
                    proofType (ParseExt _ _ _) = "Extensional proof"
                    proofType (ParseCases _ _ _) = "Case analysis proof"

            -- UTILITY
            --------------------------------------------------------------
            matchManyCases :: [ParseCase] -> [ParseCase] -> Err ()
            matchManyCases bpCases solCases = compareMany
                "Number of cases doesn't match."
                matchCases
                bpCases solCases
                where
                    matchCases :: ParseCase -> ParseCase -> Err ()
                    matchCases bp sol = errCtxt context $ do
                        compareEq "Case term mismatch:" unparseRawTermPretty
                            (pcCons bp) (pcCons sol)
                        
                        compareMany
                            "Number of fixed variables doesn't match."
                            (compareEq "Fixed variable mismatch:" assumpDoc)
                            (fromMaybe [] $ pcFixs bp)
                            (fromMaybe [] $ pcFixs sol)

                        compareMany
                            "Number of generalizing variables doesn't match."
                            (compareEq "Generalization variable mismatch:" assumpDoc)
                            (fromMaybe [] $ pcGens bp)
                            (fromMaybe [] $ pcGens sol)

                        -- TODO: A bit ugly to use compareMany and convert to list
                        compareMany
                            "Number of 'To Show' doesn't match."
                            (compareEq "'To show' mismatch:" unparseRawPropPretty)
                            (fromMaybe [] $ fmap (\e -> [e]) $ pcToShow bp)
                            (fromMaybe [] $ fmap (\e -> [e]) $ pcToShow sol)

                        compareMany
                            "Number of case assumptions doesn't match."
                            compareCaseAssumps
                            (pcAssms bp) (pcAssms sol)
                        
                        matchProofs (pcProof bp) (pcProof sol)
                        where
                            context = hsep 
                                [ text "While comparing cases"
                                , quotes $ unparseRawTermPretty $ pcCons bp
                                ]

                            compareCaseAssumps ::
                                    Named ([Assump], RawProp)
                                ->  Named ([Assump], RawProp)
                                ->  Err ()
                            compareCaseAssumps bp sol = errCtxt context $ do
                                compareEq "Assumption name mismatch." text
                                    (namedName bp) (namedName sol)
                                compareEq "Assumption proposition mismatch."
                                    unparseRawPropPretty
                                    (snd $ namedVal bp) (snd $ namedVal sol)
                                compareMany
                                    "Number of generalization variables doesn't match."
                                    (compareEq "Generalization variable mismatch." assumpDoc)
                                    (fst $ namedVal bp) (fst $ namedVal sol)
                                where
                                    context = hsep 
                                        [ text "While comparing case assumptions"
                                        , quotes $ text $ namedName bp
                                        ]

