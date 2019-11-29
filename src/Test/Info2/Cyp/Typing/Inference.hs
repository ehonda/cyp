module Test.Info2.Cyp.Typing.Inference where

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Functor.Identity -- REMOVE AFTER REFACTOR
import Data.List (union, nub, intersect, intercalate)
import Text.PrettyPrint (Doc, text)


import qualified Language.Haskell.Exts.Simple.Syntax as Exts
import qualified Test.Info2.Cyp.Term as CT
import Test.Info2.Cyp.Util -- Err functionality

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

prettyKind :: Kind -> String
prettyKind Star = "*"
prettyKind (Kfun Star k) = "* -> " ++ prettyKind k
prettyKind (Kfun k@(Kfun _ _) k') = concat 
    ["(", prettyKind k, ")", prettyKind k']

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

isFuncType :: Type -> Bool
isFuncType (TAp (TAp arr _) _)
    | arr == tArrow = True
    | otherwise = False
isFuncType _ = False

list :: Type -> Type
list t = TAp tList t

pair :: Type -> Type -> Type
pair a b = TAp (TAp tTuple2 a) b

prettyType :: Type -> String
-- Special conversion for arrow, list and tuple
prettyType (TAp (TAp arr a) b) | arr == tArrow
    = concat [prettyA, " -> ", prettyType b]
    where
        prettyA = if isFuncType a
            then concat ["(", prettyType a, ")"]
            else prettyType a

prettyType (TAp list a) | list == tList
    = concat ["[", prettyType a, "]"]
prettyType (TAp (TAp tuple a) b ) | tuple == tTuple2
    = concat ["(", prettyType a, ", ", prettyType b, ")"]
-- Regular conversion
prettyType (TVar (Tyvar id _)) = id
prettyType (TCon (Tycon id _)) = id
-- TAp on the right has to be parenthesised
prettyType (TAp s t@(TAp _ _)) = 
    concat [prettyType s, " (", prettyType t, ")"]
prettyType (TAp s t) = concat [prettyType s, " ", prettyType t]
prettyType (TGen i) = concat ["v", show i]


-- Decomposes an n-ary function a -> b -> ... -> r into args and ret type
-- ([a, b, ...], r) where non-function types t are treated as 0-ary functions
-- and therefore return ([], t)
decomposeFuncType :: Type -> ([Type], Type)
decomposeFuncType t@(TAp (TAp _ a) b)
    | isFuncType t = 
        let (rest, target) = if isFuncType b
            then decomposeFuncType b
            else ([], b)
        in (a : rest, target)
    | otherwise = ([], t)
decomposeFuncType t = ([], t)


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

-- Error transformer type
type ErrT = Except Doc   -- TODO: Change String to Doc

merge :: Subst -> Subst -> ErrT Subst
merge s s' =
    if agree
    then return (s ++ s')
    else throwE $ text "Merge fails"
    where
        agree = all subsEqual tvInter
        subsEqual = \u -> apply s (TVar u) == apply s' (TVar u)
        tvInter = map fst s `intersect` map fst s'

-- merge :: Subst -> Subst -> Err Subst
--merge :: Monad m => Subst -> Subst -> m Subst
--merge s1 s2 = if agree then return (s1 ++ s2) else fail "merge fails"
--    where agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v)) (map fst s1 `intersect` map fst s2)
    
-- Example subs (CAN BE REMOVED LATER)
---------------------------------

tvA = Tyvar "a" Star
tvB = Tyvar "b" Star
tvC = Tyvar "c" Star
tvarA = TVar $ tvA
tvarB = TVar $ tvB
tvarC = TVar $ tvC
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

--mgu :: Monad m => Type -> Type -> m Subst
--varBind :: Monad m => Tyvar -> Type -> m Subst

mgu :: Type -> Type -> ErrT Subst
mgu (TAp l r) (TAp l' r') = do 
    s1 <- mgu l l'
    s2 <- mgu (apply s1 r) (apply s1 r')
    return (s2 @@ s1)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu (TCon tc1) (TCon tc2) | tc1 == tc2 = return nullSubst
--mgu t t' = fail $ concat
mgu t t' = throwE $ text $ concat 
    [ "types do not unify: t = "
    , prettyType t
    , ", t' = "
    , prettyType t
    ]

varBind :: Tyvar -> Type -> ErrT Subst
varBind u t 
    | t == TVar u       = return nullSubst
--    | u `elem` tv t     = fail "occurs check fails"
--    | kind u /= kind t  = fail "kinds do not match"
    | u `elem` tv t     = throwE $ text $ concat 
        [ "Occurs check fails. u = "
        , prettyType $ TVar u
        , " is a type variable in t = "
        , prettyType t
        ]
    | kind u /= kind t  = throwE $ text $ concat
        [ "Kinds do not match. u = "
        , prettyType $ TVar u
        , "is of kind: "
        , prettyKind $ kind u
        , ", t = "
        , prettyType t
        , "is of kind: "
        , prettyKind $ kind t
        ]
    | otherwise         = return (u +-> t)
    
-- match
--
-- Match: Find sub s, st. apply s t1 = t2
---------------------------------

match :: Type -> Type -> ErrT Subst

match (TAp l r) (TAp l' r') = do
    sl <- match l l'
    sr <- match r r'
    merge sl sr

match (TVar u) t | kind u == kind t = return (u +-> t)
match (TCon t) (TCon t') | t == t' = return nullSubst
match t t' = throwE $ text $ concat
    [ "Types do not match: t = "
    , prettyType t
    , ", t' = "
    , prettyType t'
    ]


-- match :: Type -> Type -> Err Subst
--match :: Monad m => Type -> Type -> m Subst
--
--match (TAp l r) (TAp l' r') = do
--    sl <- match l l'
--    sr <- match r r'
--    merge sl sr
--    
--match (TVar u) t | kind u == kind t = return (u +-> t)
--match (TCon tc1) (TCon tc2) | tc1 == tc2 = return nullSubst
--match t1 t2 = fail "types do not match"


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

quantifyAll :: Type -> Scheme
quantifyAll t = quantify (tv t) t

toScheme :: Type -> Scheme
toScheme t = Forall [] t

prettyScheme :: Scheme -> String
prettyScheme (Forall ks t) = 
    concat [tvString, prettyType t] 
        where
            gens = take (length ks) $ map TGen [0..]
            prettyGens = map prettyType gens
            gensComma = intercalate ", " prettyGens

            tvString = if not $ null ks
                then concat ["forall ", gensComma, ". "]
                else ""


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
    
--schemeFromAssumps :: Monad m => Id -> [Assump] -> m Scheme
--schemeFromAssumps i [] = fail $ "unbound identifier: " ++ i
--schemeFromAssumps i ((i' :>: sc) : as) = if i == i' then return sc else schemeFromAssumps i as
schemeFromAssumps :: Id -> [Assump] -> ErrT Scheme
schemeFromAssumps i [] = throwE $ text $ "Unbound identifier: " ++ i
schemeFromAssumps i ((i' :>: sc) : as) = 
    if i == i' then return sc else schemeFromAssumps i as

prettyAssump :: Assump -> String
prettyAssump (i :>: sc) = concat [i, " :>: ", prettyScheme sc]

-- SECTION 10 (Type Inference Monad)
--------------------------------------------------------------
--------------------------------------------------------------

type TIState = (Subst, Int)
nullTIState :: TIState
nullTIState = (nullSubst, 0)

--type TI = StateT TIState Identity
type TI = StateT TIState ErrT
    
--runTI :: TI a -> ErrT a
runTI :: TI a -> Err a
runTI f = runExcept $ evalStateT f nullTIState

getSubst :: TI Subst
getSubst = gets fst

unify :: Type -> Type -> TI ()
unify t1 t2 = do
    s <- getSubst
    u <- lift $ mgu (apply s t1) (apply s t2)
    extSubst u
    where
        extSubst :: Subst -> TI ()
        extSubst s' = modify $ \(s, n) -> (s' @@ s, n)
    
newTVar :: Kind -> TI Type
newTVar k = do
    (s, n) <- get
    put (s, n + 1)
    return $ TVar $ Tyvar (enumId n) k

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

-- Type inference for Pattern
---------------------------------

data Pat = PVar Id
    | PLit Exts.Literal
    | PCon Assump [Pat]
    deriving Show
    -- PList?

    
tiPat :: Pat -> TI ([Assump], Type)

-- Variable pattern
tiPat (PVar i) = do
    v <- newTVar Star
    return ([i :>: toScheme v], v)

-- Literal pattern
tiPat (PLit l) = do
    t <- tiRawTerm [] (CT.Literal l)
    return ([], t)

-- Constructor pattern
tiPat (PCon (i :>: sc) pats) = do
    (as, ts) <- tiPats pats
    t' <- newTVar Star
    t <- freshInst sc
    unify t (foldr fn t' ts)
    return (as, t')

-- Multiple patterns
tiPats :: [Pat] -> TI ([Assump], [Type])
tiPats pats = do
    asts <- mapM tiPat pats
    let as = concat [as' | (as', _) <- asts]
        ts = [t | (_, t) <- asts]
    return (as, ts)

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
    sc <- lift $ schemeFromAssumps x as
    freshInst sc

-- Schematic
--tiRawTerm as (CT.Schematic x) = newTVar Star
tiRawTerm as (CT.Schematic x) = do
    sc <- lift $ schemeFromAssumps x as
    freshInst sc 

-- Const
tiRawTerm as (CT.Const x) = do
    sc <- lift $ schemeFromAssumps x as
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
tiTerm as (CT.Free (s, _)) = tiRawTerm as (CT.Free s)
tiTerm as (CT.Schematic (s, _)) = tiRawTerm as (CT.Schematic s)
tiTerm as (CT.Const s) = tiRawTerm as (CT.Const s)
tiTerm as (CT.Application e f) = do
    te <- tiTerm as e
    tf <- tiTerm as f
    t <- newTVar Star
    unify (tf `fn` t) te
    return t


-- Type inference for Alts
---------------------------------

type Alt = ([Pat], CT.Term)

tiAlt :: Infer Alt Type
tiAlt as (pats, term) = do
    (as', ts) <- tiPats pats
    t <- tiTerm (as' ++ as) term
    return $ foldr fn t ts

tiAlts :: [Assump] -> [Alt] -> Type -> TI ()
tiAlts as alts t = do
    ts <- mapM (tiAlt as) alts
    mapM_ (unify t) ts


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

-- Show Substition

showSub as t = do
    tiRawTerm as t
    getSubst

runAndSub as t = runTI $ f as t where
    f = \as t -> do
        ti <- tiRawTerm as t
        s <- getSubst
        return $ apply s ti

runAndSubPat p = runTI $ f p where
    f = \p -> do
        (as, t) <- tiPat p
        s <- getSubst
        return (as, apply s t)


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
