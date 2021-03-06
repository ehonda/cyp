module Test.Info2.Cyp.Types where

import Control.Monad (liftM, liftM2)
--import qualified Data.List as L (find, (\\))
import Data.List (find, (\\), nub)
import qualified Data.Map.Strict as M
import qualified Language.Haskell.Exts.Simple.Syntax as Exts
import Text.PrettyPrint

import Test.Info2.Cyp.Typing.Inference

import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Util

-- TODO: Make typed, untyped env?
data Env = Env
    { datatypes :: [DataType]
    , explicitBindings :: [ExplicitBinding]
    , implicitBindings :: [ImplicitBinding]
    , axioms :: [Named Prop]
    , constants :: [String]
    , fixes :: M.Map String Integer
    , goals :: [Prop]
    }
    deriving Show

data DataType = DataType
    { dtScheme :: Scheme
    , dtConss :: [Assump]
    }
    deriving (Eq, Show)

dataTypeDoc :: DataType -> Doc
dataTypeDoc dt = vcat 
    [ capIndent 
        "Type Constructor:" 
        [ text $ prettyScheme $ dtScheme dt ]
    , capIndent 
        "Data Constructors:" $ 
        map (text . prettyAssump') $ dtConss dt
    ]

defaultDataTypes :: [DataType]
defaultDataTypes = 
    [ DataType
        { dtScheme = scListA
        , dtConss = 
            [ ("[]" :>: scListA)
            , (":" :>: quantifyAll (tvarA `fn` tListA `fn` tListA))
            ] 
        }
    ]
    where
        tvarA = TVar (Tyvar "a" Star)
        tListA = TAp tList tvarA
        scListA = quantifyAll tListA


data Named a = Named String a
    deriving Show

instance Eq a => Eq (Named a) where
    n == m = (namedName n == namedName m)
        && (namedVal n == namedVal m)

data TConsArg = TNRec | TRec deriving (Show,Eq)

{- Types -------------------------------------------------------------}

-- Convert a parsed Exts.DataDecl into a Cyp-DataType
-- We only want to allow this form:
--      DataDecl DataType Nothing dh cons []
-- where dh is a valid dataHead
--toCypDataType :: Exts.Decl -> Err DataType
toCypDataType (Exts.DataDecl Exts.DataType Nothing dh cons [])
    | validDataHead dh = do
        tvars <- collectTVars dh []
        tyname <- tynameFromDH dh

        let -- The kind of the type constructor is 
            --  * -> ... -> *   with |tv| arrows
            -- e.g. :k (T a b) = * -> * > *
            tcKind = foldr Kfun Star $ replicate (length tvars) Star
            tcon = TCon $ Tycon tyname tcKind 
            dtype = foldl TAp tcon tvars
            dtScheme = quantifyAll dtype

        dcons <- traverse (processDCon tvars dtype) cons
        return $ DataType dtScheme dcons
    where
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
        tynameFromDH (Exts.DHead name) = return $ extractName name
        tynameFromDH (Exts.DHApp head _ ) = tynameFromDH head
        -- This branch should never be reached since we fail earlier
        -- by disallowing them in the parse (validDataHead)
        tynameFromDH _ = errStr "Could not extract typename"

        collectTVars dh tvars = case dh of
            Exts.DHead _ -> return tvars
            Exts.DHApp dh' (Exts.UnkindedVar name) -> do
                tvars' <- collectTVars dh' tvars
                let tv = TVar (Tyvar (extractName name) Star)
                return $ tvars' ++ [tv]
            -- TODO: What to do about KindedVar?
            _ -> errStr "Invalid DataHead" -- Should not happen

        -- Convert data constructors into internal representation
        -- We can ignore the first two arguments to QualConDecl since we
        -- do not allow existential quantification
        --processDCon tvs tyname (Exts.QualConDecl _ _ (Exts.ConDecl name targs)) = do
        processDCon tvs dtype (Exts.QualConDecl _ _ (Exts.ConDecl name targs)) = do
            cargs <- mapM toCypType targs
            checkForUnbounds tvs cargs
            let conType = foldr fn dtype cargs
            return $ (extractName name) :>: (quantifyAll conType)
        
        processDCon _ _ _ = errStr "Invalid data constructor"

        -- Checks for unbound type variables in cargs
        checkForUnbounds boundTVs cargs = do
            let filt = \t -> case t of
                    TVar _ -> True
                    _ -> False
                cvars = filter filt cargs
            if all (`elem` boundTVs) cvars 
            then do
                return ()
            else
                -- TODO: MORE INFO IN ERR MESSAGE
                errStr "Unbound type variable in data Declaration"

-- TODO: MORE INFO
toCypDataType _ = errStr "Invalid data declaration."

-- Converts Exts.Type to CypType, assumes all TV are of kind *
toCypType :: Exts.Type -> Err Type
toCypType (Exts.TyVar name) = return $ TVar $ Tyvar (extractName name) Star

-- It is correct to always use kind Star here, because type constructors
-- of higher kinds will be parsed as TyApp a b, and that branch of the
-- conversion function tracks the depth
toCypType (Exts.TyCon qname) = return $ TCon $ 
    Tycon (extractQName qname) Star

-- Special case for lists
toCypType (Exts.TyList t) = do
    t' <-  toCypType t
    return $ TAp tList t'
    where

--toCypType (Exts.TyApp tc arg) = liftM2 TAp (toCypType tc) (toCypType arg)
toCypType (Exts.TyApp a b) = liftM2 TAp (convertTCAps 1 a) (toCypType b)
    where
        convertTCAps depth (Exts.TyCon qname) = 
            return $ TCon $ Tycon (extractQName qname) $ makeKind depth
        convertTCAps depth (Exts.TyApp a' b') =
            liftM2 TAp (convertTCAps (depth + 1) a') (toCypType b')

        makeKind depth = foldr Kfun Star $ replicate depth Star


toCypType (Exts.TyParen t) = toCypType t
toCypType (Exts.TyFun a b) = fn <$> toCypType a <*> toCypType b
-- TODO: DO WE NEED TO MATCH MORE CONSTRUCTORS?
toCypType _ = errStr "Type can not be converted to Cyp-Type"

{- ENv -------------------------------------------------------------}

-- Convert Exts.Pat to our custom Pat. Needs
-- an environment that contains constructors
-- and their types, to find the assumps for PCon.

convertExtsPat :: [Assump] -> Exts.Pat -> Err Pat
convertExtsPat _ (Exts.PVar v) = return $ PVar $ extractName v
convertExtsPat _ (Exts.PLit Exts.Signless l) = return $ PLit l

convertExtsPat consAs (Exts.PInfixApp p1 qName p2) =
    convertExtsPat consAs (Exts.PApp qName [p1, p2])

convertExtsPat consAs (Exts.PApp qName ps) =
    case find (hasName dconName) consAs of
        Just dconAssump -> do
            pats <- traverse (convertExtsPat consAs) ps
            return $ PCon dconAssump pats
        Nothing -> errStr $ "Data Constructor of unknown Type: " ++ dconName
    where 
        dconName = extractQName qName
        hasName name (i :>: _) = name == i

convertExtsPat consAs (Exts.PParen p) = convertExtsPat consAs p

-- PList gets translated into according PCon
convertExtsPat consAs (Exts.PList []) =
    convertExtsPat consAs (Exts.PApp nil [])
    where
        nil = (Exts.UnQual (Exts.Ident "[]"))

-- TODO: HANDLE NON-EMPTY CASE
-- These are pattern of the form [1, 2, 3] - NOT: (x:xs)

--convertExtsPat consAs (Exts.PList (p:ps)) =
--    convertExtsPat consAs (Exts.PInfixApp p cons (Exts.PList ps))
--    where
--        cons = (Exts.UnQual (Exts.Ident ":"))

--    convertExtsPat consAs (Exts.PApp (Exts.UnQual (Exts.Ident ":")) ps)

-- TODO: Better error messages, like in translatePat?
convertExtsPat _ p = errStr $ "Unsupported pattern type: " ++ show p


-- Alt types
---------------------------------------------------

-- TODO: Many of these are not needed anymore?
type RawAlt = ([Exts.Pat], Term)
type FunctionRawAlts = (String, [RawAlt])
type FunctionAlts = (String, [Alt])

--type FunRawAlts = Named [RawAlt]    -- A function f and it's alts

convertRawAlt :: [Assump] -> RawAlt -> Err Alt
convertRawAlt consAs (pats, rhs) = do
    pats' <- traverse (convertExtsPat consAs) pats
    return (pats', rhs) 


getConsAssumptions :: [DataType] -> [Assump]
getConsAssumptions dts = dconsAs
    where
        dconsAs = concat $ map dtConss dts

convertFunctionRawAlts :: [Assump] -> FunctionRawAlts -> Err FunctionAlts
convertFunctionRawAlts consAs (name, rawAlts) = do
    alts <- traverse (convertRawAlt consAs) rawAlts
    return (name, alts)

--------------------------------------------------------
-- TODO: USE EITHER EXTRACT[Q]NAME OR (FROM TERM.HS)
--       TRANSLATE[Q]NAME EVERYWHERE!

-- Extract name String out of a Exts.Name (might be done better, ok for now)
extractName (Exts.Ident s) = s
extractName (Exts.Symbol s) = s

extractQName (Exts.UnQual n) = extractName n
-- Special
extractQName (Exts.Special (Exts.ListCon)) = "[]"
extractQName (Exts.Special (Exts.Cons)) = ":"
-- TODO: Handle unitcon etc

--extractQName _ = _
-- TODO HANDLE QUAl, SPECIAL
--------------------------------------------------------


-- Converts Data Constructor from (String, Type) to (String, [TConsArg])
-- as in the old DataType 
toOldDataConstructor :: (String, Type) -> (String, [TConsArg])
toOldDataConstructor (dcName, dcType) =
    (dcName, map (toTConsArg dt) argList)
    where
        (argList, dt) = decomposeFuncType dcType
        toTConsArg dataType argType
            | dataType == argType = TRec
            | otherwise = TNRec

{- Equation sequences ------------------------------------------------}

data EqnSeq a = Single a | Step a String (EqnSeq a) deriving Show
data EqnSeqq a = EqnSeqq (EqnSeq a) (Maybe (EqnSeq a)) deriving Show

instance Foldable EqnSeq where
    foldMap f (Single x) = f x
    foldMap f (Step x _ es) = f x `mappend` foldMap f es

instance Functor EqnSeq where
    fmap f (Single x) = Single (f x)
    fmap f (Step x y es) = Step (f x) y (fmap f es)

instance Traversable EqnSeq where
    traverse f (Single x) = Single <$> f x
    traverse f (Step x y es) = Step <$> f x <*> pure y <*> traverse f es

instance Foldable EqnSeqq where
    foldMap f (EqnSeqq x Nothing) = foldMap f x
    foldMap f (EqnSeqq x (Just y)) = foldMap f x `mappend` foldMap f y

instance Functor EqnSeqq where
    fmap f (EqnSeqq x y) = EqnSeqq (fmap f x) (fmap f <$> y)

instance Traversable EqnSeqq where
    traverse f (EqnSeqq x Nothing) = EqnSeqq <$> (traverse f x) <*> pure Nothing
    traverse f (EqnSeqq x (Just y)) = EqnSeqq <$> (traverse f x) <*> (Just <$> traverse f y)


eqnSeqFromList :: a -> [(String,a)] -> EqnSeq a
eqnSeqFromList a [] = Single a
eqnSeqFromList a ((b', a') : bas) = Step a b' (eqnSeqFromList a' bas)

-- x (by a1) .=. y  =>  [(x, a1), (y, "")]
eqnSeqToList :: EqnSeq a -> [(a, String)]
eqnSeqToList seq = accumulate seq []
    where
        accumulate (Single a) xs = xs ++ [(a, "")]
        accumulate (Step a rule rest) xs =
            accumulate rest $ xs ++ [(a, rule)]

-- x (by a1) .=. y  =>  [("", x), (a1, y)]
eqnSeqToList' :: EqnSeq a -> [(String, a)]
eqnSeqToList' seq = accumulate seq "" []
    where
        accumulate (Single a) rule xs = xs ++ [(rule, a)]
        accumulate (Step a rule rest) lastRule xs =
            accumulate rest rule $ xs ++ [(lastRule, a)] 

eqnSeqEnds :: EqnSeq a -> (a,a)
eqnSeqEnds (Single x) = (x,x)
eqnSeqEnds (Step a _ es) = (a, snd $ eqnSeqEnds es)

eqnSeqHead :: EqnSeq a -> a
eqnSeqHead (Single x) = x
eqnSeqHead (Step x _ _) = x

eqnSeqqHead :: EqnSeqq a -> a
eqnSeqqHead (EqnSeqq eqns _) = eqnSeqHead eqns

getVarsEqnSeqq :: EqnSeqq Term -> [String]
getVarsEqnSeqq eqns = nub $ concat $ fmap getVars eqns

-- Shortened equation seq display, that is
--                 x
--  (by rule1) .=. ...
--  (by rulen) .=. z
shortenedEqnSeqDoc :: (a -> Doc) -> EqnSeq a -> Doc
shortenedEqnSeqDoc toDoc seq = process $ eqnSeqToList' seq
    where
        process [(_, single)] = toDoc single
        process seq@[(_, start), (rule, end)] = vcat
            [ nest (maxNest + 10) $ toDoc start
            , ruleDoc rule <+> text symPropEq <+> toDoc end
            ]
            where
                maxNest = maxRuleLen $ map fst $ seq

        process ((_, start):rest) = vcat
            [ nest (maxNest + 10) $ toDoc start
            , ruleDoc firstRule <+> text ((pad firstIndent) ++ symPropEq) 
                <+> text "..."
            , ruleDoc lastRule <+> text ((pad lastIndent) ++ symPropEq) 
                <+> toDoc end
            ]
            where
                (firstRule, _) = head rest
                (lastRule, end) = last rest

                rules = [firstRule, lastRule]
                maxNest = maxRuleLen $ rules
                [firstIndent, lastIndent] = indentAfterRule 
                    rules

                pad n = concat $ replicate n " "

        -- Impossible match
        process [] = empty
                
        ruleDoc :: String -> Doc
        ruleDoc rule = text $ concat ["(by ", rule, ")"]

        ruleLens :: [String] -> [Int]
        ruleLens = map length
        maxRuleLen = maximum . ruleLens
        indentAfterRule rules = map ((maxRuleLen rules) -) $ ruleLens rules

{- Named operations --------------------------------------------------}

instance Foldable Named where
    foldMap f (Named _ x) = f x

instance Functor Named where
    fmap f (Named n x) = Named n (f x)

instance Traversable Named where
    traverse f (Named n x) = Named n <$> f x

namedVal :: Named a -> a
namedVal (Named _ a) = a

namedName :: Named a -> String
namedName (Named name _) = name
