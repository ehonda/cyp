import Test.Info2.Cyp

import Control.Monad
import Data.List (elem)
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure, exitSuccess)
import Text.PrettyPrint (render)

-- UGLY, TEMPORARY -> for now used to print theory type info
import Test.Info2.Cyp.Typing.Theory (printTheoryTypeInfo)

main :: IO ()
main = do
    args <- getArgs
    -- TODO: COULD BE DONE CLEANER
    -- Typecheck only theory file
    when (length args == 1) $ do
        let [thyFile] = args
        result <- typeCheckTheoryFile thyFile
        case result of
            Left e -> do
                putStrLn $ render e
                exitFailure
            Right tti -> do
                printTheoryTypeInfo tti
                exitSuccess

    -- Typecheck and proofcheck
    when (length args == 2) $ do
        let [thyFile, prfFile] = args
        result <- proofFile thyFile prfFile
        case result of
            Left e -> do
                putStrLn $ render e
                exitFailure
            Right () -> do
                putStrLn "Congratulations! You correctly proved all goals!"
                exitSuccess

    -- Blueprint for theory
    when (length args == 3) $ do
        let [bpThyFile, solThyFile, solPrfFile] = args
        result <- proofFileBlueprint 
            bpThyFile solThyFile Nothing solPrfFile
        case result of
            Left e -> do
                putStrLn $ render e
                exitFailure
            Right () -> do
                putStrLn $ "Congratulations! Solution matches Blueprint and"
                    ++ " You correctly proved all goals!"
                exitSuccess

    -- Blueprint for theory and proof
    when (length args == 4) $ do
        let [bpThyFile, solThyFile, bpPrfFile, solPrfFile] = args
        result <- proofFileBlueprint 
            bpThyFile solThyFile (Just bpPrfFile) solPrfFile
        case result of
            Left e -> do
                putStrLn $ render e
                exitFailure
            Right () -> do
                putStrLn $ "Congratulations! Solution matches Blueprint and"
                    ++ " You correctly proved all goals!"
                exitSuccess

    -- Wrong syntax message
    unless ((length args) `elem` [1, 2, 4]) $ do
        prog <- getProgName
        putStrLn "To prove all goals, using provided Theory and Proof:"
        putStrLn $ "Syntax: " ++ prog ++ " <background.cthy> <proof.cprf>"
        putStrLn ""
        putStrLn "To typecheck only the provided Theory:"
        putStrLn $ "Syntax: " ++ prog ++ " <background.cthy>"
        putStrLn ""
        putStrLn "To match blueprint theory and prove all goals:"
        putStrLn $ "Syntax: " ++ prog ++ " bpThy solThy solPrf"
        putStrLn ""
        putStrLn "To match blueprint theory and proof and prove all goals:"
        putStrLn $ "Syntax: " ++ prog ++ " bpThy solThy bpPrf solPrf"
        putStrLn ""
        exitFailure
    
