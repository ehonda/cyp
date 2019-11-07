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

import Data.Char
import Data.Maybe
import Text.Parsec as Parsec
import qualified Language.Haskell.Exts.Simple.Parser as P
import qualified Language.Haskell.Exts.Simple.Syntax as Exts
import qualified Language.Haskell.Exts.Pretty as ExtsPretty
import Text.PrettyPrint (quotes, text, (<+>))

import Test.Info2.Cyp.Env
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Util

data ParseDeclTree
    = DataDecl String
    | SymDecl String
    | Axiom String String
    | FunDef String
    | Goal String
    | TypeSig String String     -- Symbol, Type
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
    = ParseInduction String RawTerm [RawTerm] [ParseCase] -- data type, induction variable, generalized variables, cases
    | ParseEquation (EqnSeqq RawTerm)
    | ParseExt RawTerm RawProp ParseProof -- fixed variable, to show, subproof
    | ParseCases String RawTerm [ParseCase] -- data type, term, cases
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

typeSigParser :: Parsec [Char] () ParseDeclTree
typeSigParser = do
    sym <- trim <$> toDoubleColon
    sig <- trim <$> toEol
    return $ TypeSig sym sig

equationProofParser :: Parsec [Char] Env ParseProof
equationProofParser = fmap ParseEquation equationsParser

varParser = fmap (\v -> if v `elem` defaultConsts then Const v else Free v) idParser
varsParser = varParser `sepBy1` (keyword ",")

inductionProofParser :: Parsec [Char] Env ParseProof
inductionProofParser = do
    keyword "on"
    datatype <- many1 (noneOf " \t\r\n" <?> "datatype")
    lineSpaces
    over <- varParser
    manySpacesOrComment
    gens <- option [] (do
      keyword "generalizing"
      lineSpaces
      varsParser)
    manySpacesOrComment
    cases <- many1 caseParser
    manySpacesOrComment
    return $ ParseInduction datatype over gens cases

caseProofParser :: Parsec [Char] Env ParseProof
caseProofParser = do
    keyword "on"
    datatype <- many1 (noneOf " \t")
    lineSpaces
    over <- termParser defaultToFree
    manySpacesOrComment
    cases <- many1 caseParser
    manySpacesOrComment
    return $ ParseCases datatype over cases

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
termParser mode = flip label "term" $ do
    s <- trim <$> toEol1 <?> "expression"
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

toDoubleColon :: Parsec [Char] u String
toDoubleColon = manyTill anyChar doubleColon

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


--readDataType :: [ParseDeclTree] -> Err [DataType]
--readDataType = sequence . mapMaybe parseDataType
--  where
--    parseDataType (DataDecl s) = Just $ errCtxt (text "Parsing the datatype declaration" <+> quotes (text s)) $ do
--        (tycon : dacons) <- traverse parseCons $ splitStringAt "=|" s []
--        tyname <- constName $ fst $ stripComb tycon
--        dacons' <- traverse (parseDacon tycon) dacons
--        return $ DataType tyname dacons'
--    parseDataType _ = Nothing
--
--    parseCons :: String -> Err Term
--    parseCons = iparseTerm (\x -> Right $ Free (x, 0))
--
--    constName (Const c) = return c
--    constName term = errStr $ "Term '" ++ show term ++ "' is not a constant."
--
--    parseDacon tycon term = do
--        let (con, args) = stripComb term
--        name <- constName con
--        args' <- traverse (parseDaconArg tycon) args
--        return (name, args')
--
--    parseDaconArg tycon term | term == tycon = return TRec
--    parseDaconArg _ (Application _ _) = errStr $ "Nested constructors (apart from direct recursion) are not allowed."
--    parseDaconArg _ (Literal _) = errStr $ "Literals not allowed in datatype declarations"
--    parseDaconArg _ _ = return TNRec

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

dataDeclStr (DataDecl s) = "data " ++ s

-- This will use parseDecl to parse the declaration
-- We want datatype declarations, i.e. this constructor:
--      DataDecl l (DataOrNew l) (Maybe (Context l)) (DeclHead l) [QualConDecl l] [Deriving l]
-- Specifically, we only want to allow this form:
--      DataDecl l (DataType l) Nothing dh cons []
-- that is, no newtypes, no context, no deriving and additional constraints on datatype etc
readDataType :: [ParseDeclTree] -> Err [DataType]
readDataType = sequence . mapMaybe parseDataType
--readDataTypeFixed = sequence . mapMaybe parseDataType
    where
        parseDataType (DataDecl s) = Just $ errCtxt (text "Parsing the datatype declaration" <+> quotes (text s)) $
            -- The 'data' keyword consumed by the datatype parser needs to be
            -- added again. This also means that we can't get a newtype
            -- declaration out of this parse, therefore we need not be concerned
            -- about that possibility
            case P.parseDecl $ "data " ++ s of
                P.ParseOk (Exts.DataDecl _ Nothing dh cons []) | validDataHead dh -> do
                    tyname <- typeName dh
                    dacons <- traverse (convertDataCon tyname) cons
                    return $ DataType tyname dacons
                P.ParseOk (Exts.DataDecl _ (Just context) _ _ _) -> 
                    errMsg "Context for type parameters is not allowed."
                P.ParseOk (Exts.DataDecl _ _ dh _ _) | (not . validDataHead) dh ->
                    errMsg "Invalid declaration head." 
                P.ParseOk (Exts.DataDecl _ _ _ _ derivs) ->
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

        -- Extracts the typename from a datahead declaration
        typeName (Exts.DHead name) = return $ extractName name
        typeName (Exts.DHApp head _ ) = typeName head
        -- This branch should never be reached since we fail earlier
        -- by disallowing them in the parse (validDataHead)
        typeName _ = errStr "Could not extract typename"

        -- Convert data constructors into internal representation
        -- We can ignore the first two arguments to QualConDecl since we
        -- do not allow existential quantification
        convertDataCon tyname (Exts.QualConDecl _ _ (Exts.ConDecl name typeArgs)) = do
            cypArgs <- traverse (convertToCypArg tyname) typeArgs
            return (extractName name, cypArgs)
        -- TODO: HANDLING OF INFIX AND RECORD CONSTRUCTORS

        
        -- Converts Type Argument to Cyp Type Argument
        convertToCypArg tyname (Exts.TyVar name) = return TNRec
        -- TODO: HANDLE QUALIFIED AND SPECIAL NAMES
        -- Unqualified Type Constructor
        convertToCypArg tyname (Exts.TyCon (Exts.UnQual name))
                | extractName name == tyname = return TRec
                | otherwise = return TNRec
        -- Qualified Type Constructor (Disallowed)
        convertToCypArg tyname con@(Exts.TyCon (Exts.Qual _ _)) =
            errCtxtStr "Qualified Names are not allowed:" $ 
                err $ ExtsPretty.prettyPrim con
        -- Special [TODO]

        convertToCypArg tyname (Exts.TyParen arg) = convertToCypArg tyname arg
        -- TODO: HANDLE SPECIAL NAMES
        convertToCypArg tyname (Exts.TyApp (Exts.TyCon (Exts.UnQual name)) _)
            | extractName name == tyname = return TRec
            | otherwise = return TNRec
        convertToCypArg _ (Exts.TyFun _ _) = return TNRec
        convertToCypArg _ con = errCtxtStr "Illegal Data Constructor Argument" $
            err $ ExtsPretty.prettyPrim con
        -- TODO: What to do with tuple, sum types etc, LIST!, see
        --  http://hackage.haskell.org/package/haskell-src-exts-1.21.1/docs/Language-Haskell-Exts-Syntax.html#t:Type


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


readFunc :: [String] -> [ParseDeclTree] -> Err ([Named Prop], [String])
readFunc syms pds = do
    rawDecls <- sequence . mapMaybe parseFunc $ pds
    let syms' = syms ++ map (\(sym, _, _) -> sym) rawDecls
    props0 <- traverse (declToProp syms') rawDecls
    let props = map (fmap $ generalizeExceptProp []) props0
    return (props, syms')
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

splitStringAt :: Eq a => [a] -> [a] -> [a] -> [[a]]
splitStringAt _ [] h
    | h == [] = []
    | otherwise = h : []
splitStringAt a (x:xs) h
    | x `elem` a = h : splitStringAt a xs []
    | otherwise = splitStringAt a xs (h++[x])
