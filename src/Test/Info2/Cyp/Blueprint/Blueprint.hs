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

-- Utility
rawTermDoc :: String -> RawTerm -> Doc
rawTermDoc name t = eqDoc name $ render $ unparseRawTerm t

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
        errMsg bp term = capIndent
            "Mismatch between blueprint and term"
            [ rawTermDoc "blueprint" bp
            , rawTermDoc "term" term
            ]

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
            | otherwise = err $ errMsg bp term


--matchBlueprintWithProp :: Prop -> Prop -> Err ()
--matchBlueprintWithProp (Prop bpLhs bpRhs) (Prop lhs rhs) = do
--    matchBlueprintWithTerm bpLhs lhs
--    matchBlueprintWithTerm bpRhs rhs

-- Match theories
--------------------------------------------------------

matchBlueprintWithTheory :: String -> String -> Err ()
matchBlueprintWithTheory blueprint theory = 
    errCtxtStr "While matching blueprint with theory" $ do
        (bpDts, bpSigs, bpFuns, bpAxs, bpGls) <-
            getTheoryContents readFuncBlueprint blueprint "Parsing blueprint"
        (thyDts, thySigs, thyFuns, thyAxs, thyGls) <-
            getTheoryContents readFunc theory "Parsing solution"

        -- Compare Datatypes
        compareDataTypes bpDts thyDts

        -- Match sigs
        compareTypeSignatures bpSigs thySigs

        -- Match functions
        zipWithM_ matchBlueprintWithFunction bpFuns thyFuns
        
        -- Match axioms
        compareAxioms bpAxs thyAxs

        -- Match goals
        compareGoals bpGls thyGls

        return ()
        where
            -- Duplication from Cyp.hs, refactor!
            getTheoryContents readFunc thy context = errCtxtStr context $ do
                res <- eitherToErr $ Parsec.parse cthyParser "" thy
                dts <- fmap (++ defaultDataTypes) $ readDataType res
                sigs <- readTypeSigs res
                syms <- fmap (defaultConsts ++) $ readSym res
                (_, consts, funsRawAlts) <- readFunc syms res
                axs <- readAxiom consts res
                gls <- readGoal consts res
                return (dts \\ defaultDataTypes, sigs, funsRawAlts, axs, gls)

            matchBlueprintWithAlt :: RawAlt -> RawAlt -> Err ()
            matchBlueprintWithAlt (bpPats, bpTerm) (pats, term) = do
                when (bpPats /= pats) $
                    errStr "Function pattern mismatch"
                matchBlueprintWithTerm bpTerm term

            matchBlueprintWithFunction :: FunctionRawAlts
                -> FunctionRawAlts -> Err ()
            matchBlueprintWithFunction 
                (bpName, bpAlts) (name, alts) = do
                    when (bpName /= name) $
                        errStr "Function name mismatch"
                    zipWithM_ matchBlueprintWithAlt bpAlts alts

            --compareAxioms :: Named Prop -> Named Prop -> Err ()
            --compareAxioms (Named n p) (Named n' p') = do
            --    when (n /= n') $
            --        errStr "Axiom names mismatch"
            --    when (p /= p') $
            --        errStr "Axiom props mismatch"

            comparisonDoc :: String -> (a -> Doc) -> a -> a -> Doc
            comparisonDoc header toDoc blueprint solution =
                capIndent
                    header
                    [ capIndent "Blueprint:" [toDoc blueprint]
                    , capIndent "Solution:" [toDoc solution]
                    ]

            compare :: (a -> a -> Bool)
                -> String 
                -> (a -> Doc)
                -> a -> a -> Err ()
            compare cmp header toDoc blueprint solution = 
                when (not $ cmp blueprint solution) $ err $ 
                    comparisonDoc header toDoc blueprint solution
   
            compareMany :: (a -> a -> Bool) 
                -> String 
                -> String 
                -> (a -> Doc) 
                -> [a] -> [a] -> Err ()
            compareMany cmp msgLenMismatch msgCmpMismatch toDoc bps sols = do
                when (length bps /= length sols) $ err $
                    hcat $ map text $
                        [ msgLenMismatch
                        , " Blueprint has "
                        , show $ length bps
                        , ", Solution has "
                        , show $ length sols
                        , "."
                        ]
                zipWithM_ (compare cmp msgCmpMismatch toDoc) bps sols

            compareManyEq :: Eq a => String -> String -> (a -> Doc) 
                -> [a] -> [a] -> Err ()
            compareManyEq msgLenMismatch msgCmpMismatch toDoc bps sols =
                compareMany (==) msgLenMismatch msgCmpMismatch toDoc bps sols

            compareDataTypes :: [DataType] -> [DataType] -> Err ()
            compareDataTypes bps sols = compareManyEq
                "Number of datatypes doesn't match."
                "Datatype mismatch:"
                dataTypeDoc
                bps sols

            compareTypeSignatures :: [Assump] -> [Assump] -> Err ()
            compareTypeSignatures bps sols = compareManyEq
                "Number of type signatures doesn't match."
                "Type signature mismatch:"
                assumpDoc
                bps sols

            compareAxioms :: [Named Prop] -> [Named Prop] -> Err ()
            compareAxioms bps sols = compareManyEq
                "Number of axioms doesn't match."
                "Axiom mismatch:"
                axiomDoc
                bps sols
                where
                    axiomDoc (Named n a) = (text $ n ++ ":") <+>
                        unparsePropPretty a

            compareGoals :: [Prop] -> [Prop] -> Err ()
            compareGoals bps sols = compareManyEq
                "Number of goals doesn't match."
                "Goal mismatch:"
                unparsePropPretty
                bps sols

            --compareFunctions :: [FunctionRawAlts] 
            --    -> [FunctionRawAlts] -> Err ()
            --compareFunctions bps sols = compareMany
            --    "Number of function declarations doesn't match."
            --    "Function declaration mismatch:"
            --    funcDoc
            --    bps sols
            --    where
            --        funcDoc (f, alts) = 