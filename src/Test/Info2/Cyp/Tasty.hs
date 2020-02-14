{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}

module Test.Info2.Cyp.Tasty (
  CypTest(..)
, findTests
) where

import Data.List
import Data.Tagged (Tagged(..))
import Data.Typeable (Typeable)
import qualified Test.Info2.Cyp as Cyp
import Test.Info2.Cyp.Util
import Test.Tasty
import Test.Tasty.Providers
import Text.PrettyPrint (empty, render, text, ($+$))
import System.Directory
import System.FilePath


data CypTest = CypTest { theory :: FilePath
                       , proof :: FilePath
                       } deriving Typeable

data CypTestBlueprint = CypTestBlueprint
  { bpTheory :: FilePath
  , solTheory :: FilePath
  , bpProof :: FilePath
  , solProof :: FilePath
  } deriving Typeable

instance IsTest CypTest where
  testOptions = Tagged []
  run _ t _ = either (testFailed . render) (const $ testPassed "Proof is valid") <$> Cyp.proofFile (theory t) (proof t)

instance IsTest CypTestBlueprint where
  testOptions = Tagged []
  run _ t _ = either (testFailed . render) (const $ testPassed "Proof is valid") 
    <$> Cyp.proofFileBlueprint (bpTheory t) (solTheory t) (Just $ bpProof t) (solProof t)

data NegCypTest = NegCypTest FilePath CypTest deriving Typeable
data NegCypTestBlueprint = NegCypTestBlueprint FilePath CypTestBlueprint 
  deriving Typeable

instance IsTest NegCypTest where
  testOptions = Tagged []
  run _ (NegCypTest expected t) _ =
    Cyp.proofFile (theory t) (proof t) >>= \case
      Left failure -> checkExpectedFailure expected failure
      Right () ->
        return $ testFailed "Proof is valid, but expected failure"

instance IsTest NegCypTestBlueprint where
  testOptions = Tagged []
  run _ (NegCypTestBlueprint expected t) _ =
    Cyp.proofFileBlueprint (bpTheory t) (solTheory t) (Just $ bpProof t) (solProof t) 
      >>= \case
        Left failure -> checkExpectedFailure expected failure
        Right () ->
          return $ testFailed "Proof is valid, but expected failure"

checkExpectedFailure expected failure = do
  contents <- readFile expected
  let doc = foldr ($+$) empty $ map text $ lines contents
  return $
    if contents /= render failure then
      testFailed $ render $
        text "Proof is invalid as expected, but with the wrong error message" `indent`
          (text "Expected failure:" `indent` doc $+$ text "Actual failure:" `indent` failure)
    else
      testPassed "Proof is invalid as expected"

findTests :: FilePath -> IO TestTree
findTests path = do
  allPos <- findAll pos
  allNeg <- findAll neg
  allPosBP <- findAll posBP
  allNegBP <- findAll negBP
  return $ testGroup ("Tests for " ++ show path)
    [ testGroup "Valid proofs" $ map (mkPos pos) allPos
    , testGroup "Invalid proofs" $ map (mkNeg neg) allNeg
    , testGroup "Valid proofs blueprint" $ map (mkPosBP posBP) allPosBP
    , testGroup "Invalid proofs blueprint" $ map (mkNegBP negBP) allNegBP
    ]
  where pos = path </> "pos"
        neg = path </> "neg"
        posBP = path </> "pos-blueprint"
        negBP = path </> "neg-blueprint"

        findAll path =
          filter (not . isPrefixOf ".") <$> getDirectoryContents path

        mkTest root item = CypTest { theory = root </> item </> "cthy", proof = root </> item </> "cprf" }
        mkNeg root item = singleTest item $ NegCypTest (root </> item </> "cout") $ mkTest root item
        mkPos root item = singleTest item $ mkTest root item

        mkTestBP root item = CypTestBlueprint
          { bpTheory = root </> item </> "bpthy"
          , solTheory = root </> item </> "cthy"
          , bpProof = root </> item </> "bpprf"
          , solProof = root </> item </> "cprf"
          }
        mkNegBP root item = singleTest item $ NegCypTestBlueprint
          (root </> item </> "cout") $
          mkTestBP root item
        mkPosBP root item = singleTest item $ mkTestBP root item

