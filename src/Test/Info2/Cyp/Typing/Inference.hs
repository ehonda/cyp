module Test.Info2.Cyp.Typing.Inference where

-- TODO: BREAK UP THIS LARGE MODULE INTO SUB MODULES

import Prelude hiding ((<>))
import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap, replicateM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Maybe (fromMaybe)
import Data.List (union, nub, intersect, intercalate, (\\))
import Text.PrettyPrint (Doc, text, (<>), ($$), hcat, vcat, nest)


import qualified Language.Haskell.Exts.Simple.Syntax as Exts
import qualified Language.Haskell.Exts.Pretty as ExtsPretty
import qualified Test.Info2.Cyp.Term as CT
import Test.Info2.Cyp.Util -- Err functionality
--import Test.Info2.Cyp.Typing.Pretty

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

isFuncType :: Type -> Bool
isFuncType (TAp (TAp arr _) _)
    | arr == tArrow = True
    | otherwise = False
isFuncType _ = False

list :: Type -> Type
list t = TAp tList t

pair :: Type -> Type -> Type
pair a b = TAp (TAp tTuple2 a) b

-- Decomposes an n-ary function a -> b -> ... -> r into args and ret type
-- ([a, b, ...], r) where non-function types t are treated as 0-ary functions
-- and therefore return ([], t)
decomposeFuncType :: Type -> ([Type], Type)
decomposeFuncType t@(TAp (TAp _ a) b)
    | isFuncType t = (a : rest, target)
    where
        (rest, target) = decomposeFuncType b
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
    apply s (TVar u) = fromMaybe (TVar u) $ lookup u s
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
-- TODO: MOVE TO A BETTER PLACE
type ErrT = Except Doc

merge :: Subst -> Subst -> ErrT Subst
merge s s' =
    if agree
    then return (s ++ s')
    else throwE $ text "Merge fails" -- TODO: Could show where substs disagree
    where
        agree = all subsEqual tvInter
        subsEqual = \u -> apply s (TVar u) == apply s' (TVar u)
        tvInter = map fst s `intersect` map fst s'


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

mgu :: Type -> Type -> ErrT Subst
mgu (TAp l r) (TAp l' r') = do 
    s1 <- mgu l l'
    s2 <- mgu (apply s1 r) (apply s1 r')
    return (s2 @@ s1)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu (TCon tc1) (TCon tc2) | tc1 == tc2 = return nullSubst
mgu t s = throwE $ indent
    (text "Types do not unify:")
    ((typeDoc "t" t) $$ (typeDoc "s" s))

varBind :: Tyvar -> Type -> ErrT Subst
varBind u t 
    | t == TVar u       = return nullSubst
    | u `elem` tv t     = throwE $ indent
        (text "Occurs check fails. u is a type variable in t:")
        ((typeDoc "u" (TVar u)) $$ (typeDoc "t" t)) 

    | kind u /= kind t  = 
        let tU = TVar u
            uDoc = (nest 5 $ typeDoc "u" tU) $$ (kindDoc "u" tU)
            tDoc = (nest 5 $ typeDoc "t" t) $$ (kindDoc "t" t)
        in throwE $ indent
            (text "Kinds do not match:")
            (uDoc $$ tDoc)


    | otherwise         = return (u +-> t)
    
-- Match: Find sub s, st. apply s t1 = t2
---------------------------------

match :: Type -> Type -> ErrT Subst

match (TAp l r) (TAp l' r') = do
    sl <- match l l'
    sr <- match r r'
    merge sl sr

match (TVar u) t | kind u == kind t = return (u +-> t)
match (TCon t) (TCon t') | t == t' = return nullSubst
match t s = throwE $ indent
    (text "Types do not match:")
    ((typeDoc "t" t) $$ (typeDoc "s" s)) 

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

-- Examples (CAN BE REMOVED LATER)
---------------------------------

-- TODO: MOVE THESE SOMEWHERE ELSE (Maybe where the defaults are created)
-- forall a . [a]
tsListA = quantify [tvA] $ list $ TVar tvA

-- (:) :: a -> [a] -> [a]
tsCons = quantify [tvA] $ tA `fn` ((list tA) `fn` (list tA))
    where tA = TVar tvA

-- SECTION 9 (Assumptions)
--------------------------------------------------------------
--------------------------------------------------------------

data Assump = Id :>: Scheme deriving (Eq, Show)

instance Types Assump where
    apply s (i :>: sc) = i :>: (apply s sc)
    tv (i :>: sc) = tv sc
    
schemeFromAssumps :: Id -> [Assump] -> ErrT Scheme
schemeFromAssumps i [] = throwE $ text $ "Unbound identifier: " ++ i
schemeFromAssumps i ((i' :>: sc) : as) = 
    if i == i' then return sc else schemeFromAssumps i as

hasName :: Id -> Assump -> Bool
hasName i (j :>: _) = i == j

nameEq :: Assump -> Assump -> Bool
nameEq (i :>: _) (j :>: _) = i == j

-- SECTION 10 (Type Inference Monad)
--------------------------------------------------------------
--------------------------------------------------------------

type TIState = (Subst, Int)
nullTIState :: TIState
nullTIState = (nullSubst, 0)

type TI = StateT TIState ErrT
    
runTI :: TI a -> Err a
runTI f = runExcept $ evalStateT f nullTIState

getSubst :: TI Subst
getSubst = gets fst

unifyWithExceptTransform :: Type -> Type -> (Doc -> Doc) -> TI ()
unifyWithExceptTransform t t' errTransform = do
    s <- getSubst
    u <- lift $ withExcept (errTransform' s) $
        mgu (apply s t) (apply s t')
    extSubst u
    where
        expectedActual s = indent
            (text "While unifying:")
            (      (typeDoc "expected" (apply s t)) 
                $$ (typeDoc "actual" (apply s t')))

        errTransform' s = errTransform . (indent (expectedActual s))

        extSubst :: Subst -> TI ()
        extSubst s' = modify $ \(s, n) -> (s' @@ s, n)

unifyWithErrMsg :: Type -> Type -> Doc -> TI ()
unifyWithErrMsg t t' errMsg = 
    unifyWithExceptTransform t t' prependErrMsg
    where
        prependErrMsg = indent errMsg

unify :: Type -> Type -> TI ()
unify t t' = unifyWithExceptTransform t t' id
    
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
tiPat p@(PCon conA@(i :>: sc) pats) = do
    -- Check if the right amount of
    -- argument patterns were provided
    t <- freshInst sc
    let expArgs = length (fst (decomposeFuncType t))
        actArgs = length pats
    if expArgs /= actArgs
    then lift $ throwE $ errWrongArgNumber expArgs actArgs
    else do
        -- Check if types agree
        (as, ts) <- tiPats pats
        t' <- newTVar Star
        unifyWithErrMsg t (foldr fn t' ts) errMsg
        return (as, t')
    where
        errMsg = capIndent
            "While inferring the type of a constructor pattern:"
            [patDoc "p" p, assumpDoc conA]

        errWrongArgNumber exp act = indent errMsg $ 
            text $ concat 
                [ "Wrong number of arguments in p. Expected = "
                , show exp
                , ", Actual = "
                , show act
                , "."
                ]

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
        tiLit l = lift $ throwE $ text $ concat
            ["Unsupported literal: ", show l]

-- Free
tiRawTerm as (CT.Free x) = do
    sc <- lift $ schemeFromAssumps x as
    freshInst sc

-- Schematic
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
tiTerm as term@(CT.Application e f) = do
    te <- tiTerm as e
    tf <- tiTerm as f
    t <- newTVar Star
    unifyWithErrMsg (tf `fn` t) te errMsg
    return t
    where
        errMsg = (text "While inferring the type of the term ")
            <> CT.unparseTerm term


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
    -- TODO: UNIFY WITH ERROR MESSAGE
    mapM_ (unify t) ts


-- TYPE INFERENCE FOR BINDINGS
--------------------------------------------------------------------
--------------------------------------------------------------------

-- Explicit Bindings (with type signature)
---------------------------------------------------------
type ExplicitBinding = (Assump, [Alt])

tiExplBind :: [Assump] -> ExplicitBinding -> TI ()
tiExplBind as (sig@(i :>: sc), alts) = do
    -- Instantiate the scheme and check if
    -- alts agree with that type
    t <- freshInst sc
    tiAlts as' alts t
    s <- getSubst

    -- Check if inferred scheme agrees with
    -- the provided type signature
    let t' = apply s t
        fs = tv $ apply s as'   -- fixed vars
        gs = (tv t') \\ fs      -- generic vars
        sc' = quantify gs t'
    if sc /= sc' 
    then lift $ throwE $ errMsg (i :>: sc') sig
    else return ()
    where
        as' = sig : as

        errMsg :: Assump -> Assump -> Doc
        errMsg a@(f :>: _) sig = capIndent 
            (concat 
                [ "Inferred type of "
                , f
                , " is incompatible with its type signature:"])
            [ (text "expected = ") <> assumpDoc sig
            , (text "inferred = ") <> assumpDoc a]


-- Implict Bindings (no type signature provided)
---------------------------------------------------------

type ImplicitBinding = (Id, [Alt])

tiImplBinds :: Infer [ImplicitBinding] [Assump]
tiImplBinds as binds = do
    -- Make new tvars and assumptions about
    -- those tvars (to support polymorphic
    -- recursions) for all binds
    funTypes <- replicateM (length binds) $ newTVar Star
    let ids = map fst binds
        scs = map toScheme funTypes
        as' = (zipWith (:>:) ids scs) ++ as
        --as' = as ++ (zipWith (:>:) ids scs)
        funAlts = map snd binds

    -- Infer types and return type schemes
    mapM (\(alts, t) -> tiAlts as' alts t) $
        zip funAlts funTypes
    s <- getSubst
    let funTypes' = apply s funTypes
        fs = tv $ apply s as
        vss = map tv funTypes'
        gs = foldr1 union vss \\ fs
        scs' = map (quantify gs) funTypes'
    return $ zipWith (:>:) ids scs'

-- TODO: MOVE THIS INTO OTHER MODULE
-- PRETTY PRINT FOR DIFFERENT TYPES
--------------------------------------------------------------------
--------------------------------------------------------------------

-- Kind
------------------------------------------------
prettyKind :: Kind -> String
prettyKind Star = "*"
prettyKind (Kfun Star k) = "* -> " ++ prettyKind k
prettyKind (Kfun k@(Kfun _ _) k') = concat 
    ["(", prettyKind k, ")", prettyKind k']

-- Type
------------------------------------------------
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

-- Scheme
------------------------------------------------
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

-- Assump
------------------------------------------------
prettyAssump :: Assump -> String
prettyAssump (i :>: sc) = concat [i, " :>: ", prettyScheme sc]

prettyAssump' :: Assump -> String
prettyAssump' (i :>: sc) = concat [i, " :: ", prettyScheme sc]

-- Pat
------------------------------------------------
prettyPat :: Pat -> String
prettyPat (PVar x) = x
prettyPat (PLit l) = ExtsPretty.prettyPrint l
prettyPat (PCon (c :>: _) ps) = intercalate " " $ c : (map prettyPat ps)



-- DOC FUNCTIONS FOR ERROR SIGNALING
--------------------------------------------------------------------
--------------------------------------------------------------------

typeDoc :: String -> Type -> Doc
typeDoc name t = eqDoc name $ prettyType t

kindDoc :: String -> Type -> Doc
kindDoc name t = (text "kind ") <> (eqDoc name $ prettyType t)

eqDoc :: String -> String -> Doc
eqDoc lhs rhs = hcat $ map text $ [lhs, " = ", rhs]

patDoc :: String -> Pat -> Doc
patDoc name p = eqDoc name $ prettyPat p

assumpDoc :: Assump -> Doc
assumpDoc a = text $ prettyAssump' a

capIndent :: String -> [Doc] -> Doc
capIndent cap docs = indent (text cap) $ vcat docs
