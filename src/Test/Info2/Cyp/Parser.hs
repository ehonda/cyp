{-# LANGUAGE FlexibleContexts #-} -- ONLY FOR TEST PARSE FUNCTIONS

module Test.Info2.Cyp.Parser where
-- Export everythin while testing
--    ( ParseLemma (..)
--    , ParseCase (..)
--    , ParseProof (..)
--    , cthyParser
--    , cprfParser
--    , readAxiom
--    , readDataType
--    , readFunc
--    , readGoal
--    , readSym
--    )
--where

import Control.Monad (when)
import Data.Char
import Data.Maybe
import Data.List (nub)
import Text.Parsec as Parsec
import qualified Language.Haskell.Exts.Simple.Parser as P
import qualified Language.Haskell.Exts.Simple.Syntax as Exts
--import qualified Language.Haskell.Exts.Pretty as ExtsPretty -- NOT NEEDED?
import Text.PrettyPrint (quotes, text, (<+>), render)

import Test.Info2.Cyp.Env
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Util
--import Test.Info2.Cyp.Types     -- ONLY FOR TESTING, REMOVE AGAIN!
import Test.Info2.Cyp.Typing.Inference (Assump(..), quantifyAll, prettyType, Scheme(..)) -- prettyType ONLY FOR TESTING!

data ParseDeclTree
    = DataDecl String
    | SymDecl String
    | Axiom String String
    | FunDef String
    | Goal String
    | TypeSig String
    deriving Show

data ParseLemma = ParseLemma String RawProp ParseProof -- Proposition, Proof
    deriving Show

data ParseCase = ParseCase
    { pcCons :: RawTerm
    , pcFixs :: Maybe [RawTerm] -- fixed variables
    , pcGens :: Maybe [RawTerm] -- generalized variables
    , pcToShow :: Maybe RawProp -- goal
    , pcAssms :: [Named ([RawTerm], RawProp)] -- (generalized variables, assumption)
    , pcProof :: ParseProof
    }
    deriving Show

data ParseProof
    = ParseInduction Assump [RawTerm] [ParseCase] -- (over :: Type), generalized variables, cases
    | ParseEquation (EqnSeqq RawTerm)
    | ParseExt RawTerm RawProp ParseProof -- fixed variable, to show, subproof
--    | ParseCases String RawTerm [ParseCase] -- data type, term, cases
--    | ParseCases Assump [ParseCase] -- (over :: Type), cases
    | ParseCases Scheme RawTerm [ParseCase] -- term typescheme, term, cases
    | ParseCheating
    deriving Show


trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

toParsec :: (a -> String) -> Either a b -> Parsec c u b
toParsec f = either (fail . f) return

-- Test Functions
----------------------------------------------------------------

testParse parser file = do
    content <- readFile file
    print $ parse parser "test" content

testParseStr parser str = print $ parse parser "test" str

{- Custom combinators ------------------------------------------------}

notFollowedBy' :: (Stream s m t, Show a) => ParsecT s u m a -> String -> ParsecT s u m ()
notFollowedBy' p msg = try $ (try p >> unexpected msg) <|> return ()

sepBy1' :: (Stream s m t) => ParsecT s u m a -> ParsecT s u m String -> ParsecT s u m (EqnSeq a)
sepBy1' p sep = do
    x <- p
    xs <- many ((,) <$> sep <*> p)
    return $ eqnSeqFromList x xs


{- Parser ------------------------------------------------------------}
eol :: Parsec [Char] u ()
eol = do
    _ <- try (string "\n\r") <|> try (string "\r\n") <|> string "\n" <|> string "\r" -- <|> (eof >> return "")
        <?> "end of line"
    return ()

doubleColon :: Parsec [Char] u ()
doubleColon = do
    string "::"
    return ()


toDoubleColon :: Parsec [Char] u String
toDoubleColon = manyTill valid doubleColon
    where
        end = eof <|> eol <|> commentParser
        -- Check no new line or comment is beginning
        invalid = notFollowedBy' end "end of line or comment"
        valid = (try invalid) >> anyChar

lineBreak :: Parsec [Char] u ()
lineBreak = (eof <|> eol <|> commentParser) >> manySpacesOrComment

idParser :: Parsec [Char] u String
idParser = idP <?> "Id"
  where
    idP = do
        c <- letter
        cs <- many (char '_' <|> alphaNum)
        lineSpaces
        return (c:cs)

commentParser :: Parsec [Char] u ()
commentParser = p <?> "comment"
  where
    p = do
        _ <- try (string "--")
        _ <- many (noneOf "\r\n")
        eol <|> eof
        return ()

cthyParser :: Parsec [Char] () [ParseDeclTree]
cthyParser =
    do result <- many cthyParsers
       eof
       return result

cthyParsers :: Parsec [Char] () ParseDeclTree
cthyParsers =
    do manySpacesOrComment
       result <- 
            (goalParser 
            <|> dataParser 
            <|> axiomParser 
            <|> symParser
            <|> try typeSigParser 
            <|> try funParser)
       return result

keywordToEolParser :: String -> (String -> a) -> Parsec [Char] () a
keywordToEolParser s f =
    do  keyword s
        result <- trim <$> toEol
        return (f result)

axiomParser :: Parsec [Char] () ParseDeclTree
axiomParser = do
    keyword "axiom"
    name <- idParser
    char ':'
    xs <- trim <$> toEol
    return $ Axiom name xs

dataParser :: Parsec [Char] () ParseDeclTree
dataParser = keywordToEolParser "data" DataDecl

goalParser :: Parsec [Char] () ParseDeclTree
goalParser = keywordToEolParser "goal" Goal

symParser :: Parsec [Char] () ParseDeclTree
symParser = keywordToEolParser "declare_sym" SymDecl

funParser :: Parsec [Char] () ParseDeclTree
funParser = do
    cs <- toEol1 <?> "Function definition"
    return (FunDef cs)

-- TODO: REWORK, UGLY CODE
--typeSigParser :: Parsec [Char] () ParseDeclTree
typeSigParser :: Parsec [Char] u ParseDeclTree
typeSigParser = do
    -- This could be done cleaner
    sym <- trim <$> toDoubleColon
    sig <- trim <$> toEolOrGens <?> "Type Signature"
    return $ TypeSig $ concat [sym, " :: ", sig]
    where
        end = (try $ lookAhead $ keyword "generalizing") <|> 
            eof <|> eol <|> commentParser
        -- Check no new line or comment is beginning
        invalid = notFollowedBy' end "end of line or comment"
        valid = (try invalid) >> anyChar
        
        toDoubleColon :: Parsec [Char] u String
        toDoubleColon = manyTill valid doubleColon

        toEolOrGens :: Parsec [Char] u String
        toEolOrGens = do
            notFollowedBy' end "end of line or comment"
            x <- anyChar
            xs <- manyTill anyChar end
            return (x : xs)
          where
            end = (try $ lookAhead $ keyword "generalizing") <|> 
                eof <|> eol <|> commentParser

equationProofParser :: Parsec [Char] Env ParseProof
equationProofParser = fmap ParseEquation equationsParser

varParser = fmap (\v -> if v `elem` defaultConsts then Const v else Free v) idParser
varsParser = varParser `sepBy1` (keyword ",")

inductionProofParser :: Parsec [Char] Env ParseProof
inductionProofParser = do
    keyword "on"
    sig <- typeSigParser
    manySpacesOrComment
    gens <- option [] (do
      keyword "generalizing"
      lineSpaces
      varsParser)
    manySpacesOrComment
    cases <- many1 caseParser
    manySpacesOrComment

    -- Read typesig right here and fail if its invalid
    case readTypeSigRequireExactlyOneId sig of
        Left err -> unexpected $ render err
        Right sig' -> return $ ParseInduction sig' gens cases

caseProofParser :: Parsec [Char] Env ParseProof
caseProofParser = do
    keyword "on"
    --datatype <- many1 (noneOf " \t")
    --lineSpaces
    --over <- termParser defaultToFree
    --sig <- typeSigParser

    -- Read term with type attached, eg
    --      p x :: Bool
    -- Only parse until double colon here
    over <- termParserUntil toEolOrDoubleColon defaultToFree
    sc <- trim <$> toEol1

    manySpacesOrComment
    cases <- many1 caseParser
    manySpacesOrComment

    -- Read typesig right here and fail if its invalid
    case readTypeScheme sc of
        Left err -> unexpected $ render err
        Right sc' -> return $ ParseCases sc' over cases

cheatingProofParser :: Parsec [Char] Env ParseProof
cheatingProofParser = return ParseCheating

extProofParser :: Parsec [Char] Env ParseProof
extProofParser = do
    keyword "with"
    lineSpaces
    with <- termParser defaultToFree
    manySpacesOrComment
    toShow <- toShowParser
    manySpacesOrComment
    proof <- proofParser
    manySpacesOrComment
    return $ ParseExt with toShow proof

type PropParserMode = [String] -> String -> Err RawTerm

propParser :: PropParserMode -> Parsec [Char] Env RawProp
propParser mode = do
    s <- trim <$> toEol1 <?> "expression"
    env <- getState
    let prop = errCtxtStr "Failed to parse expression" $
            iparseProp (mode $ constants env) s
    toParsec show prop

propGenParser :: PropParserMode -> Parsec [Char] Env ([RawTerm], RawProp)
propGenParser mode = do
    gens <- option [] (do
      keyword "forall"
      gens <- varsParser
      char ':'
      lineSpaces
      return gens)
    s <- trim <$> toEol1 <?> "expression"
    env <- getState
    let prop = errCtxtStr "Failed to parse expression" $
            iparseProp (mode $ constants env) s
    prop <- toParsec show prop
    return (gens, prop)

termParser :: PropParserMode -> Parsec [Char] Env RawTerm
--termParser mode = flip label "term" $ do
--    s <- trim <$> toEol1 <?> "expression"
--    env <- getState
--    let term = errCtxtStr "Failed to parse expression" $
--            iparseTerm (mode $ constants env) s
--    toParsec show term
termParser = termParserUntil toEol1

termParserUntil toEnd mode = flip label "term" $ do
    s <- trim <$> toEnd <?> "expression"
    env <- getState
    let term = errCtxtStr "Failed to parse expression" $
            iparseTerm (mode $ constants env) s
    toParsec show term 

namedPropParser :: PropParserMode -> Parsec [Char] Env String -> Parsec [Char] Env (String, RawProp)
namedPropParser mode p = do
    name <- option "" p
    char ':'
    prop <- propParser mode
    return (name, prop)

namedPropGenParser :: PropParserMode -> Parsec [Char] Env String -> Parsec [Char] Env (String, [RawTerm], RawProp)
namedPropGenParser mode p = do
    name <- option "" p
    char ':'
    lineSpaces
    (gens, prop) <- propGenParser mode
    return (name, gens, prop)

lemmaParser :: Parsec [Char] Env ParseLemma
lemmaParser =
    do  keyword "Lemma"
        (name, prop) <- namedPropParser defaultToFree idParser
        manySpacesOrComment
        prf <- proofParser
        manySpacesOrComment
        return $ ParseLemma name prop prf

proofParser :: Parsec [Char] Env ParseProof
proofParser = do
    keyword "Proof"
    p <- choice
        [ keyword "by induction" >> inductionProofParser
        , keyword "by extensionality" >> extProofParser
        , keyword "by case analysis" >> caseProofParser
        , keyword "by cheating" >> lineBreak >> cheatingProofParser
        , lineBreak >> equationProofParser
        ]
    keywordQED
    return p

cprfParser ::  Parsec [Char] Env [ParseLemma]
cprfParser =
    do  lemmas <- many1 lemmaParser
        eof
        return lemmas

lineSpaces :: Parsec [Char] u ()
lineSpaces = skipMany (oneOf " \t") <?> "horizontal white space"

keyword :: String -> Parsec [Char] u ()
keyword kw = do
    try (string kw >> notFollowedBy (alphaNum <?> "")) <?> "keyword " ++ show kw
    lineSpaces

keywordCase :: Parsec [Char] u ()
keywordCase = keyword "Case"

keywordQED :: Parsec [Char] u ()
keywordQED = keyword "QED"

toEol :: Parsec [Char] u String
toEol = manyTill anyChar (eof <|> eol <|> commentParser)

toEol1 :: Parsec [Char] u String
toEol1 = do
    notFollowedBy' end "end of line or comment"
    x <- anyChar
    xs <- manyTill anyChar end
    return (x : xs)
  where
    end = eof <|> eol <|> commentParser

toEolOrDoubleColon :: Parsec [Char] u String
toEolOrDoubleColon = do
    notFollowedBy' end "end of line or comment"
    x <- anyChar
    xs <- manyTill anyChar end
    return (x : xs)
    where
        end = doubleColon <|> eof <|> eol <|> commentParser

byRuleParser :: Parsec [Char] u String
byRuleParser = do
    try (char '(' >>  lineSpaces >> keyword "by")
    cs <- trim <$> manyTill (noneOf "\r\n") (char ')')
    lineSpaces
    return cs

equationsParser :: Parsec [Char] Env (EqnSeqq RawTerm)
equationsParser = do
    eq1 <- equations
    eq2 <- optionMaybe (notFollowedBy keywordQED >> equations)
    return $ EqnSeqq eq1 eq2
  where
    equation = termParser defaultToFree <* manySpacesOrComment
    rule = byRuleParser <* string symPropEq <* lineSpaces
    equations = sepBy1' equation rule

toShowParser :: Parsec [Char] Env RawProp
toShowParser = do
    keyword "Show"
    char ':'
    propParser defaultToFree

caseParser :: Parsec [Char] Env ParseCase
caseParser = do
    keywordCase
    lineSpaces
    t <- termParser defaultToFree
    manySpacesOrComment
    fxs <- optionMaybe $ do
      keyword "Fix"
      varsParser <* manySpacesOrComment  
    assms <- assmsP
    manySpacesOrComment
    gens <- optionMaybe $ do
      choice [char 'f', char 'F']
      keyword "or fixed"
      varsParser <* manySpacesOrComment
    toShow <- optionMaybe (toShowParser <* manySpacesOrComment)
    manyTill anyChar (lookAhead (string "Proof"))
    proof <- proofParser
    manySpacesOrComment
    return $ ParseCase
        { pcCons = t
        , pcFixs = fxs
        , pcGens = gens
        , pcToShow = toShow
        , pcAssms = assms
        , pcProof = proof
        }
  where
    assmsP = option [] $ do
        keyword "Assume"
        manySpacesOrComment
        assms <- flip manyTill (lookAhead (string "Then")) $ do
            assm <- assmP
            manySpacesOrComment
            return assm
        keyword "Then"
        return assms
    assmP = do
        (name, gens, prop) <- namedPropGenParser defaultToFree idParser
        return $ Named (if name == "" then "assumption" else name) (gens, prop)


manySpacesOrComment :: Parsec [Char] u ()
manySpacesOrComment = skipMany $ (space >> return ()) <|> commentParser

-----------------------------------------------------------------------
-----------------------------------------------------------------------
-----------------------------------------------------------------------
-----------------------------------------------------------------------
-----------------------------------------------------------------------
-----------------------------------------------------------------------

-- READ DATATYPE TESTS
treeStr = "Tree a = Leaf a | Node a (Tree a) (Tree a)"
dtTree = DataDecl treeStr
dtWrapped = DataDecl $ "Wrapped = WT (Int -> Int)"
dtWrapped2 = DataDecl $ "Wrapped = WT (Int -> (Int -> Int))"
-- THIS IS ILLEGAL -> PROBLEM
-- Either use the version with Nil and Cons, or make lists builtin
listStr = "List a = [] | a : (List a)"
listStr' = "List a = Nil | Cons a (List a)"
dtList = DataDecl listStr
dtMixed = DataDecl "Mixed a b = AB a b | BA b a"

dtRec = DataDecl "Rec a = R (Rec a)"
dtNested = DataDecl "Nested a = N (Other a)"        -- Illegal in readDataType
dtNestedInt = DataDecl "Nested a = N Int"           -- Legal in readDataType
dtNestedList = DataDecl "NList a = N [a]"           -- Illegal in readDataType

-- Existential quantification, we do not allow this!
-- THIS WAS TEST CODE WHILE WRITING THE FUNCTION, CAN BE REMOVED
--exQStr = "Worker x b = forall b. Num b => Worker {buf :: b, input :: x}"
--
--modeExQ = P.defaultParseMode { P.extensions = [HE.EnableExtension HE.ExistentialQuantification] }

dtInfix = DataDecl "Assump = Id :>: Scheme"
dtInfixHeadFail = DataDecl "a & b = Tuple a b"
dtDerivingFail = DataDecl "Tree a = Leaf a deriving Show"
-- This does not fail, since the parser doesn't know that b is not in scope.
-- Needs to be handlded separately
dtABFail = DataDecl "Tree a = Leaf b"
dtQualArgNameFail = DataDecl "D = D OtherModule.Type"

dtListAsArg = DataDecl "D a = D [a]"

--dataDeclStr (DataDecl s) = "data " ++ s

dataBool = "data Bool = True | False"
dataList = "data L a = Nil | Cons a (L a)"
dataMixed = "data Mixed a b = AB a b | BA b a"
dataUnboundTV = "data UB = UB a"
dataABC = "data ABC a b c = ABC a b c"
dataParen = "data P a b c = P (a b) c"
dataTwoParam = "data TP a b = TP"
dataListParam = "data LP a = LP [a]"
dataOneParam = "data D a = D a"

getDataDecl decl = case P.parseDecl decl of
    P.ParseOk decl' -> decl'
    _ -> Exts.DefaultDecl []

testConv decl = toCypDataType $ getDataDecl decl

prettyConv decl = do
    dt <- testConv decl
    return $ map prettyDCon $ dtConss dt 
    where
        prettyDCon = \(dcon, dtype) -> concat 
            [dcon, " :: ", prettyType dtype]

showConv decl = case prettyConv decl of
    Left e -> print e
    Right sigs -> mapM_ print sigs
    

-- This will use parseDecl to parse the declaration
-- We want datatype declarations, i.e. this constructor:
--      DataDecl l (DataOrNew l) (Maybe (Context l)) (DeclHead l) [QualConDecl l] [Deriving l]
-- Specifically, we only want to allow this form:
--      DataDecl l (DataType l) Nothing dh cons []
-- that is, no newtypes, no context, no deriving and additional constraints on datatype etc
readDataType :: [ParseDeclTree] -> Err [DataType]
readDataType = sequence . mapMaybe parseDataType
    where
        parseDataType (DataDecl s) = Just $ errCtxt (text "Parsing the datatype declaration" <+> quotes (text s)) $
            -- The 'data' keyword consumed by the datatype parser needs to be
            -- added again. This also means that we can't get a newtype
            -- declaration out of this parse, therefore we need not be concerned
            -- about that possibility
            case P.parseDecl $ "data " ++ s of
                P.ParseOk p@(Exts.DataDecl _ Nothing dh _ []) | validDataHead dh ->
                    toCypDataType p
                P.ParseOk (Exts.DataDecl _ (Just _) _ _ _) -> 
                    errMsg "Context for type parameters is not allowed."
                P.ParseOk (Exts.DataDecl _ _ dh _ _) | (not . validDataHead) dh ->
                    errMsg "Invalid declaration head." 
                P.ParseOk (Exts.DataDecl _ _ _ _ (_:_)) ->
                    errMsg "Deriving declarations are not allowed."
                P.ParseFailed _ msg -> errMsg msg
                _ -> errMsg "Unkown Error"

                where errMsg msg = errCtxtStr "Error parsing datatype declaration" $ errStr msg
        parseDataType _ = Nothing

        -- We don't allow paren or infix expressions for the data head
        --      (i.e. D (a :< b) c)
        -- only expressions of the form
        --      D a b c
        --validDataHead (Exts.DHInfix _ _) = False
        --validDataHead (Exts.DHParen _) = False
        validDataHead (Exts.DHApp head _) = validDataHead head
        validDataHead (Exts.DHead _) = True
        validDataHead _ = False

readAxiom :: [String] -> [ParseDeclTree] -> Err [Named Prop]
readAxiom consts = sequence . mapMaybe parseAxiom
  where
    parseAxiom (Axiom n s) = Just $ do
        prop <- iparseProp (defaultToFree consts) s
        return $ Named n $ interpretProp declEnv $ generalizeExceptProp [] $ prop
    parseAxiom _ = Nothing

readGoal :: [String] -> [ParseDeclTree] -> Err [Prop]
readGoal consts = sequence . map (fmap $ interpretProp declEnv)  . mapMaybe parseGoal
  where
    parseGoal (Goal s) = Just $ iparseProp (defaultToFree consts) s
    parseGoal _ = Nothing

readSym :: [ParseDeclTree] -> Err [String]
readSym = sequence . mapMaybe parseSym
  where
    parseSym (SymDecl s) = Just $ do
        term <- iparseTerm (Right . Const) s
        case term of
            Const v -> Right v
            _ -> errStr $ "Expression '" ++ s ++ "' is not a symbol"
    parseSym _ = Nothing


-- TEST CASES READ FUNC
-----------------------------------------------------------------------

defId = FunDef "id x = x"
defPLit = FunDef "f 1 = 2"
defApp = FunDef "app x xs = xs ++ [x]"
dc = defaultConsts


--type RawAlt = ([Exts.Pat], Term)
--type FunctionRawAlts = (String, [RawAlt])

readFunc :: [String] -> [ParseDeclTree] 
    -> Err ([Named Prop], [String], [FunctionRawAlts])
readFunc syms pds = do
    rawDecls <- sequence . mapMaybe parseFunc $ pds
    let syms' = syms ++ map (\(sym, _, _) -> sym) rawDecls
    props0 <- traverse (declToProp syms') rawDecls
    let props = map (fmap $ generalizeExceptProp []) props0

        -- Assemble raw alts representation of the functions
        -- Make ungrouped raw alts
        extPats = [ps | (_, ps, _) <- rawDecls]
        rhss = [rhs | Named _ (Prop _ rhs) <- props]
        rawAlts = zip extPats rhss

        -- Group by names
        names = [name | (name, _, _) <- rawDecls]
        uniqueNames = nub names
        collectAlts name = map snd $ filter ((name ==) . fst) $ 
            zip names rawAlts
        funsRawAlts = zip uniqueNames $ map collectAlts uniqueNames
    return (props, syms', funsRawAlts)
  where

    declToProp :: [String] -> (String, [Exts.Pat], Exts.Exp) -> Err (Named Prop)
    declToProp consts (funSym, pats, rawRhs) = do
        tPat <- traverse translatePat pats
        rhs <- translateExp tv rawRhs
        let prop = interpretProp declEnv $ Prop (listComb (Const funSym) tPat) rhs
        return $ Named ("def " ++ funSym) prop
      where
        pvars = concatMap collectPVars pats
        tv s | s `elem` pvars = return $ Schematic s
             | s `elem` consts = return $ Const s
             | otherwise = errStr $ "Unbound variable '" ++ s ++ "' not allowed on rhs"

    collectPVars :: Exts.Pat -> [String]
    collectPVars (Exts.PVar v) = [translateName v]
    collectPVars (Exts.PInfixApp p1 _ p2) = collectPVars p1 ++ collectPVars p2
    collectPVars (Exts.PApp _ ps) = concatMap collectPVars ps
    collectPVars (Exts.PList ps) = concatMap collectPVars ps
    collectPVars (Exts.PParen p) = collectPVars p
    collectPVars _ = []

    parseFunc :: ParseDeclTree -> Maybe (Err (String, [Exts.Pat], Exts.Exp))
    parseFunc (FunDef s) = Just $ errCtxt (text "Parsing function definition" <+> quotes (text s)) $
        case P.parseDecl s of
            P.ParseOk (Exts.FunBind [Exts.Match name pat (Exts.UnGuardedRhs rhs) Nothing])
                -> Right (translateName name, pat, rhs)
            P.ParseOk (Exts.FunBind [Exts.InfixMatch pat0 name pat (Exts.UnGuardedRhs rhs) Nothing])
                -> Right (translateName name, pat0 : pat, rhs)
            P.ParseOk _ -> errStr "Invalid function definition."
            f@(P.ParseFailed _ _ ) -> err $ renderSrcExtsFail "declaration" f
    parseFunc _ = Nothing


--readTypeSig :: [ParseDeclTree] -> Err [Assump]
readTypeSig pdt = fmap concat $ sequence $ mapMaybe parseTypeSig pdt
    where
        parseTypeSig (TypeSig s) = Just $ 
            errCtxt (text "Parsing the type signature" <+> quotes (text s)) $
                case P.parseDecl s of
                    -- Type signatures can be specified for several
                    -- identifiers at a time, e.g:
                    --      f, g :: X -> X
                    -- that is the reason syms is a list -> in that
                    -- case we need to return assumptions for multiple
                    -- ids from one TypeSig
                    P.ParseOk (Exts.TypeSig syms t) -> do
                        t' <- toCypType t
                        return $ zipWith (:>:) ids $ schemes t'
                        where
                            ids = map extractName syms
                            schemes t = repeat $ quantifyAll t
                    _ -> errStr "Parse error"

        parseTypeSig _ = Nothing
--parseTypeSig (TypeSig s) = Just $ 
--    errCtxt (text "Parsing the type signature" <+> quotes (text s)) $
--        case P.parseDecl s of
--            -- Type signatures can be specified for several
--            -- identifiers at a time, e.g:
--            --      f, g :: X -> X
--            -- that is the reason syms is a list -> in that
--            -- case we need to return assumptions for multiple
--            -- ids from one TypeSig
--            P.ParseOk (Exts.TypeSig syms t) -> do
--                t' <- toCypType t
--                return $ zipWith (:>:) ids $ schemes t'
--                where
--                    ids = map extractName syms
--                    schemes t = repeat $ quantifyAll t
--            _ -> errStr "Parse error"
--
--parseTypeSig _ = Nothing

-- Reads the type signature in pdt, requires that the type
-- for exactly one symbol is provided
readTypeSigRequireExactlyOneId :: ParseDeclTree -> Err Assump
readTypeSigRequireExactlyOneId (TypeSig s) =
    errCtxt (text "Parsing the type signature" <+> quotes (text s)) $
        case P.parseDecl s of
            P.ParseOk (Exts.TypeSig syms t) -> do
                t' <- toCypType t
                when (length ids /= 1) $ errStr "Only one symbol expected"
                return $ (head ids) :>: (quantifyAll t')
                where
                    ids = map extractName syms

            _ -> errStr "Parse error"
readTypeSigRequireExactlyOneId _ = errStr "Not a type signature"


readTypeScheme :: String -> Err Scheme
readTypeScheme s = 
    errCtxt (text "Parsing the type scheme" <+> quotes (text s)) $
        case P.parseType s of
            P.ParseOk t -> do
                t' <- toCypType t
                return $ quantifyAll t'
            _ -> errStr "Parse Error"


splitStringAt :: Eq a => [a] -> [a] -> [a] -> [[a]]
splitStringAt _ [] h
    | h == [] = []
    | otherwise = h : []
splitStringAt a (x:xs) h
    | x `elem` a = h : splitStringAt a xs []
    | otherwise = splitStringAt a xs (h++[x])
