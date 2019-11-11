module Test.Info2.Cyp.Types where

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
        -- Traverse constypes here
        return tvars
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

        collectTVars dh tvars = case dh of
            Exts.DHead _ -> return tvars
            Exts.DHApp dh' (Exts.UnkindedVar name) -> do
                tvars' <- collectTVars dh' tvars
                return $ (TVar (Tyvar (extractName name) Star)) : tvars'
            -- TODO: What to do about KindedVar?
            _ -> errStr "Invalid DataHead" -- Should not happen

toCypDataType _ = errStr "Invalid data declaration can't be converted."

-- Extract name String out of a Exts.Name (might be done better, ok for now)
extractName (Exts.Ident s) = s
extractName (Exts.Symbol s) = s

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
