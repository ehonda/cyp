module Test.Info2.Cyp.Typing.Inference where

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)
import Data.List (union, nub, intersect, intercalate)

import qualified Language.Haskell.Exts.Simple.Syntax as Exts
import qualified Test.Info2.Cyp.Term as CT

-- SECTION 4 (TYPES)
--------------------------------------------------------------
--------------------------------------------------------------

-- Type definitions
---------------------------------

type Id = String

enumId :: Int -> Id
enumId n = "v" ++ show n

data Kind = Star | Kfun Kind Kind 
    deriving (Eq, Show)
data Type = TVar Tyvar | TCon Tycon | TAp Type Type | TGen Int
    deriving (Eq, Show)
data Tyvar = Tyvar Id Kind
    deriving (Eq, Show)
data Tycon = Tycon Id Kind
    deriving (Eq, Show)

-- Example type representations
---------------------------------

tChar = TCon $ Tycon "Char" Star
tInt = TCon $ Tycon "Int" Star
tFrac = TCon $ Tycon "Frac" Star

tList = TCon $ Tycon "[]" $ Kfun Star Star
tArrow = TCon $ Tycon "(->)" $ Kfun Star $ Kfun Star Star
tTuple2 = TCon $ Tycon "(,)" $ Kfun Star $ Kfun Star Star

tString = list tChar

-- Utility
---------------------------------

infixr 4 `fn`
fn :: Type -> Type -> Type
a `fn` b = TAp (TAp tArrow a) b

list :: Type -> Type
list t = TAp tList t

pair :: Type -> Type -> Type
pair a b = TAp (TAp tTuple2 a) b

prettyType :: Type -> String
-- Special conversion for arrow, list and tuple
prettyType (TAp (TAp arr a) b) | arr == tArrow
    = concat [prettyType a, " -> ", prettyType b]
prettyType (TAp list a) | list == tList
    = concat ["[", prettyType a, "]"]
prettyType (TAp (TAp tuple a) b ) | tuple == tTuple2
    = concat ["(", prettyType a, ", ", prettyType b, ")"]
-- Regular conversion
prettyType (TVar (Tyvar id _)) = id
prettyType (TCon (Tycon id _)) = id
--prettyType (TAp s t) = concat ["(", prettyType s, " ", prettyType t, ")"]
prettyType (TAp s t) = concat [prettyType s, " ", prettyType t]
prettyType (TGen i) = concat ["v", show i]

-- HasKind
---------------------------------

class HasKind t where
    kind :: t -> Kind
    
instance HasKind Tyvar where
    kind (Tyvar v k) = k
instance HasKind Tycon where
    kind (Tycon v k) = k
instance HasKind Type where
    kind (TVar u) = kind u
    kind (TCon tc) = kind tc
    kind (TAp t _) = case (kind t) of
        Kfun _ k -> k
        -- What to do if kind t is not kfun?


-- SECTION 5 (Substitutions etc)
--------------------------------------------------------------
--------------------------------------------------------------

-- Substitutions
---------------------------------

type Subst = [(Tyvar, Type)]

nullSubst :: Subst
nullSubst = []

(+->) :: Tyvar -> Type -> Subst
u +-> t = [(u, t)]

-- Types apply
---------------------------------

-- FIND BETTER NAME
class Types t where
    apply :: Subst -> t -> t
    tv :: t -> [Tyvar]
    
instance Types Type where
    apply s (TVar u) = case lookup u s of
        Just t -> t
        Nothing -> TVar u
    apply s (TAp l r) = TAp (apply s l) (apply s r)
    apply s t = t
    
    tv (TVar u) = [u]
    tv (TAp l r) = tv l `union` tv r
    tv t = []
    
instance Types a => Types [a] where
    apply s = map (apply s)
    tv = nub . concat . map tv
    
infixr 4 @@
(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = [(u, apply s1 t) | (u, t) <- s2] ++ s1

merge :: Monad m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return (s1 ++ s2) else fail "merge fails"
    where agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v)) (map fst s1 `intersect` map fst s2)
    
-- Example subs (CAN BE REMOVED LATER)
---------------------------------

tvA = Tyvar "a" Star
tvB = Tyvar "b" Star
tvC = Tyvar "c" Star
tvList = [TVar tvA, TVar tvA, TVar tvB, TVar tvC]
tFn_tvA_tInt = (TVar tvA) `fn` tInt

sub1 = [(tvA, tInt), (tvB, tChar)]
sub2 = [(tvC, tString)]
sub3 = [(tvA, tChar)]


-- SECTION 6 (Unification)
--------------------------------------------------------------
--------------------------------------------------------------

-- mgu, varBind
--
-- Unifier: sub s, st. for types t1 and t2: 
--              apply s t1 = apply s t2
--
-- mgu: unif u, st. any unif s = s'@@u for some sub s'
---------------------------------

mgu :: Monad m => Type -> Type -> m Subst
varBind :: Monad m => Tyvar -> Type -> m Subst

mgu (TAp l r) (TAp l' r') = do 
    s1 <- mgu l l'
    s2 <- mgu (apply s1 r) (apply s1 r')
    return (s2 @@ s1)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu (TCon tc1) (TCon tc2) | tc1 == tc2 = return nullSubst
mgu t1 t2 = fail "types do not unify"

varBind u t 
    | t == TVar u       = return nullSubst
    | u `elem` tv t     = fail "occurs check fails"
    | kind u /= kind t  = fail "kinds do not match"
    | otherwise         = return (u +-> t)
    
-- match
--
-- Match: Find sub s, st. apply s t1 = t2
---------------------------------

match :: Monad m => Type -> Type -> m Subst

match (TAp l r) (TAp l' r') = do
    sl <- match l l'
    sr <- match r r'
    merge sl sr
    
match (TVar u) t | kind u == kind t = return (u +-> t)
match (TCon tc1) (TCon tc2) | tc1 == tc2 = return nullSubst
match t1 t2 = fail "types do not match"


-- SECTION 8 (Type Schemes)
--
--  This is modified and doesn't use qualified types, since
--  we also do not use predicates (no type classes)
--------------------------------------------------------------
--------------------------------------------------------------

data Scheme = Forall [Kind] Type deriving (Eq, Show)

instance Types Scheme where
    apply s (Forall ks t) = Forall ks (apply s t)
    tv (Forall ks t) = tv t

quantify :: [Tyvar] -> Type -> Scheme
quantify vs t = Forall ks (apply s t) where
    vs' = [v | v <- tv t, v `elem` vs]
    ks = map kind vs'
    s = zip vs' (map TGen [0..])

toScheme :: Type -> Scheme
toScheme t = Forall [] t

prettyScheme :: Scheme -> String
prettyScheme (Forall ks t) = 
    concat ["forall ", gensComma, ". ", prettyType t] 
        where
            gens = take (length ks) $ map TGen [0..]
            prettyGens = map prettyType gens
            gensComma = intercalate ", " prettyGens


-- Examples (CAN BE REMOVED LATER)
---------------------------------

tsPair1 = quantify [tvA, tvB] (pair (TVar tvA) (TVar tvB))
tsPair2 = quantify [tvA, tvB, tvC] (pair (TVar tvA) (TVar tvB))

-- forall a . [a]
tsListA = quantify [tvA] $ list $ TVar tvA

-- (:) :: a -> [a] -> [a]
tsCons = quantify [tvA] $ tA `fn` ((list tA) `fn` (list tA))
    where tA = TVar tvA

-- 

-- SECTION 9 (Assumptions)
--------------------------------------------------------------
--------------------------------------------------------------

data Assump = Id :>: Scheme deriving Show

instance Types Assump where
    apply s (i :>: sc) = i :>: (apply s sc)
    tv (i :>: sc) = tv sc
    
find :: Monad m => Id -> [Assump] -> m Scheme
find i [] = fail $ "unbound identifier: " ++ i
find i ((i' :>: sc) : as) = if i == i' then return sc else find i as


-- SECTION 10 (Type Inference Monad)
--------------------------------------------------------------
--------------------------------------------------------------

newtype TI a = TI (Subst -> Int -> (Subst, Int, a))

instance Monad TI where
    return x = TI (\s n -> (s, n, x))
    TI f >>= g = TI (\s n -> case f s n of
        (s', m, x) -> let TI gx = g x in gx s' m)
        
instance Applicative TI where
    pure = return
    (<*>) = ap
    
instance Functor TI where
    fmap = liftM
    
runTI :: TI a -> a
runTI (TI f) = x where (s, n, x) = f nullSubst 0

getSubst :: TI Subst
getSubst = TI (\s n -> (s, n, s))

unify :: Type -> Type -> TI ()
unify t1 t2 = do
    s <- getSubst
    u <- mgu (apply s t1) (apply s t2)
    extSubst u
    
extSubst :: Subst -> TI ()
extSubst s' = TI (\s n -> (s' @@ s, n, ()))

newTVar :: Kind -> TI Type
newTVar k = TI (\s n ->
    let v = Tyvar (enumId n) k
    in (s, n + 1, TVar v))
    
freshInst :: Scheme -> TI Type
freshInst (Forall ks t) = do
    ts <- mapM newTVar ks
    return (inst ts t)
    
class Instantiate t where
    inst :: [Type] -> t -> t

instance Instantiate Type where
    inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
    inst ts (TGen n) = ts !! n
    inst ts t = t

instance Instantiate a => Instantiate [a] where
    inst ts = map (inst ts)


-- SECTION 11 (Type Inference)
--------------------------------------------------------------
--------------------------------------------------------------

type Infer e t = [Assump] -> e -> TI t

-- Type inference for Terms
---------------------------------

tiRawTerm :: Infer CT.RawTerm Type

-- Literals
tiRawTerm as (CT.Literal l) = tiLit l
    where
        -- See unparesLiteral in Term.hs, add support for Prim Variants
        tiLit (Exts.Char _) = return tChar
        tiLit (Exts.String _) = return tString
        tiLit (Exts.Int _) = return tInt
        tiLit (Exts.Frac _) = return tFrac

-- Free
tiRawTerm as (CT.Free x) = do
    sc <- find x as
    freshInst sc
    
-- Const
tiRawTerm as (CT.Const x) = do
    sc <- find x as
    freshInst sc

-- Application
tiRawTerm as (CT.Application e f) = do
    te <- tiRawTerm as e
    tf <- tiRawTerm as f
    t <- newTVar Star
    unify (tf `fn` t) te
    return t

-- Code duplication: Use Generics!
tiTerm :: Infer CT.Term Type
tiTerm as (CT.Literal l) = tiRawTerm as (CT.Literal l)
tiTerm as (CT.Free (s, n)) = tiRawTerm as (CT.Free s)
tiTerm as (CT.Const s) = tiRawTerm as (CT.Const s)
tiTerm as (CT.Application e f) = do
    te <- tiTerm as e
    tf <- tiTerm as f
    t <- newTVar Star
    unify (tf `fn` t) te
    return t


--tiTerm as = tiRawTerm as

-- TESTS (CAN BE REMOVED LATER)
---------------------------------

-- Literal
t1 = runTI $ tiRawTerm [] (CT.Literal (Exts.Char 'c'))

-- Free
t2 = runTI $ tiRawTerm ["x" :>: (toScheme tInt)] (CT.Free "x")
t3 = runTI $ tiRawTerm [] (CT.Free "x")   -- Fails

-- Const
t4 = runTI $ tiRawTerm ["f" :>: (toScheme (tInt `fn` tInt))]
    (CT.Const "f")

-- Application
t5 = runTI $ tiRawTerm ["x" :>: (toScheme tInt), "y" :>: (toScheme tInt)] 
    (CT.Application (CT.Free "x") (CT.Free "y"))     -- Fails
t6 = runTI $ tiRawTerm ["f" :>: (toScheme (tInt `fn` tInt)), "x" :>: (toScheme tInt)]
    (CT.Application (CT.Free "f") (CT.Free "x"))

-- Apptest
appAs = ["f" :>: (toScheme (tInt `fn` tInt)), "x" :>: (toScheme tInt)]
appApp = (CT.Application (CT.Free "f") (CT.Free "x"))

appTest as (CT.Application e f) = do
    te <- tiRawTerm as e
    tf <- tiRawTerm as f
    t <- newTVar Star
    unify (tf `fn` t) te
    getSubst

testApp = runTI $ appTest appAs appApp


-- Show Substition

showSub as t = do
    tiRawTerm as t
    getSubst

runAndSub as t = runTI $ f as t where
    f = \as t -> do
        ti <- tiRawTerm as t
        s <- getSubst
        return $ apply s ti


-- Trivial theory test

trivAs1 = 
    [":" :>: tsCons
    , "z" :>: (toScheme tInt)
    , "zs" :>: (toScheme (list tInt))]

trivTerm1 = CT.Application (CT.Application (CT.Const ":") (CT.Free "z")) (CT.Free "zs")

-- z : zs with expicit types (ie Int and [Int])
ttriv1 = runTI $ tiRawTerm 
    [":" :>: tsCons
    , "z" :>: (toScheme tInt)
    , "zs" :>: (toScheme (list tInt))] $ 
        CT.Application (CT.Application (CT.Const ":") (CT.Free "z")) (CT.Free "zs")

ttriv2 = runTI $ tiRawTerm [] $
    CT.Application (CT.Application (CT.Const "++") (CT.Free "zs")) (CT.Application (CT.Application (CT.Const ":") (CT.Free "z")) (CT.Const "[]"))
