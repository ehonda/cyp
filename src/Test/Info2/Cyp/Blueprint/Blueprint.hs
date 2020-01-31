module Test.Info2.Cyp.Blueprint.Blueprint where

import Control.Monad
import Data.List
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
        compareFunctions bpFuns thyFuns
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

            -- Utility to compare the various lists
            ---------------------------------------------------------
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

            compareFunctions :: [FunctionAlts] 
                -> [FunctionAlts] -> Err ()
            compareFunctions bps sols = compareMany
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
