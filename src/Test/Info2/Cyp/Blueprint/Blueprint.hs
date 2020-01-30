module Test.Info2.Cyp.Blueprint.Blueprint where

import Control.Monad
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

        -- Match Datatypes
        --when (bpDts /= thyDts) $
        --    errStr "Datatypes mismatch"
        --zipWithM_ compareDts bpDts thyDts

        -- Match sigs
        when (bpSigs /= thySigs) $
            errStr "Type signatures mismatch"

        -- Match functions
        zipWithM_ matchBlueprintWithFunction bpFuns thyFuns
        
        -- Match axioms
        --when (bpAxs /= thyAxs) $
        --    errStr "Axioms mismatch"
        --zipWithM_ matchBlueprintWithAxiom bpAxs thyAxs
        zipWithM_ compareAxioms bpAxs thyAxs

        -- Match goals
        when (bpGls /= thyGls) $
            errStr "Goals mismatch"
        --zipWithM_ matchBlueprintWithProp bpGls thyGls

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
                return (dts, sigs, funsRawAlts, axs, gls)

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

            compareAxioms :: Named Prop -> Named Prop -> Err ()
            compareAxioms (Named n p) (Named n' p') = do
                when (n /= n') $
                    errStr "Axiom names mismatch"
                when (p /= p') $
                    errStr "Axiom props mismatch"

            --comparisonDoc :: String -> (a -> Doc) -> a -> a -> Doc
            --comparisonDoc header toDoc blueprint solution =
            --    capIndent
            --        header
            --        [ capIndent "blueprint" [toDoc blueprint]
            --        , capIndent "solution" [toDoc solution]
            --        ]
--
            --compare :: Eq a => String -> (a -> Doc) -> a -> a -> Err ()
            --compare header header toDoc blueprint solution = 
            --    when (a /= b) $ err $ 
            --        comparisonDoc header toDoc blueprint solution
--
            --compareDts :: DataType -> DataType -> Err ()
            --compareDts bp sol = compare "Type mismatch" dataTypeDoc bp sol

            --compareDts = compareAndShowMismatches showMismatch a b
            --    where
            --        showMismatch a b 

            --matchBlueprintWithAxiom :: Named Prop 
            --    -> Named Prop -> Err ()
            --matchBlueprintWithAxiom bp ax = do
            --    when (namedName bp /= namedName ax) $
            --        errStr "Axiom name mismatch"
            --    matchBlueprintWithProp (namedVal bp) (namedVal ax)
