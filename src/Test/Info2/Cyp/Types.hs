module Test.Info2.Cyp.Types where

import Control.Monad (liftM, liftM2)
import qualified Data.Map.Strict as M
import qualified Language.Haskell.Exts.Simple.Syntax as Exts

import Test.Info2.Cyp.Typing.Inference

import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Util

data Env = Env
    { datatypes :: [DataType]
    , axioms :: [Named Prop]
    , constants :: [String]
    , fixes :: M.Map String Integer
    , goals :: [Prop]
    }
    deriving Show

data DataType = DataType
    { dtName :: String
    , dtConss :: [(String, [TConsArg])]
--    , dtConss :: [(String, [(TConsArg, Exts.Type)])]
    }
    deriving Show

defaultDataTypes :: [DataType]
defaultDataTypes = 
    [ DataType 
        { dtName = "List"
--        , dtConss = [("[]", []), (":", 
--            [ (TNRec, Exts.TyVar () (Exts.Ident () "a"))
--            , (TRec, Exts.TyCon () )])
--            ] 
        , dtConss = [("[]", []), (":", [TNRec, TRec])] 
        }
    ]

data Named a = Named String a
    deriving Show

data TConsArg = TNRec | TRec deriving (Show,Eq)

{- Types -------------------------------------------------------------}

-- Convert a parsed Exts.Type into a Cyp-Type
--      BETTER: Convert a whole parsed Declaration into a Cyp-Type & Cyp-DataType
--
--toCypType :: Exts.Type -> Type
--toCypType Exts.TyVar name = TVar TyVar $ (extractName name) Star
--toCypType Exts.TyCon name = TCon TyCon $ (extractName name) Star

-- Convert a parsed Exts.DataDecl into a Cyp-DataType
-- We only want to allow this form:
--      DataDecl DataType Nothing dh cons []
-- where dh is a valid dataHead
--toCypDataType :: Exts.Decl -> Err DataType
toCypDataType (Exts.DataDecl Exts.DataType Nothing dh cons [])
    | validDataHead dh = do
        tvars <- collectTVars dh []
        tyname <- tynameFromDH dh
        dcons <- traverse (processDCon tvars tyname) cons
        return (tyname, dcons)
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
        processDCon tvs tyname (Exts.QualConDecl _ _ (Exts.ConDecl name targs)) = do
            cargs <- mapM toCypType targs
            checkForUnbounds tvs cargs
            let tcon = TCon $ Tycon tyname Star 
                dtype = foldl TAp tcon tvs
                conType = foldr fn dtype cargs
            return (extractName name, conType)
        -- TODO: HANDLING OF INFIX AND RECORD CONSTRUCTORS
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
toCypType (Exts.TyCon qname) = return $ TCon $ Tycon (extractQName qname) Star
toCypType (Exts.TyApp tc arg) = liftM2 TAp (toCypType tc) (toCypType arg)
toCypType (Exts.TyParen t) = toCypType t -- IS THIS CORRECT?
-- TODO: DO WE NEED TO MATCH MORE CONSTRUCTORS?
toCypType _ = errStr "Type can not be converted to Cyp-Type"

-- Extract name String out of a Exts.Name (might be done better, ok for now)
extractName (Exts.Ident s) = s
extractName (Exts.Symbol s) = s

extractQName (Exts.UnQual n) = extractName n
--extractQName _ = _
-- TODO HANDLE QUAl, SPECIAL

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

eqnSeqEnds :: EqnSeq a -> (a,a)
eqnSeqEnds (Single x) = (x,x)
eqnSeqEnds (Step a _ es) = (a, snd $ eqnSeqEnds es)

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
