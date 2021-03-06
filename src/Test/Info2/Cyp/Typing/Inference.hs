module Test.Info2.Cyp.Typing.Inference where

-- TODO: BREAK UP THIS LARGE MODULE INTO SUB MODULES

import Prelude hiding ((<>))
import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap, replicateM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Maybe (fromMaybe)
import Data.List (union, nub, intersect, intercalate, (\\), intersperse)
import Text.PrettyPrint (Doc, text, hsep, (<>), ($$), hcat, vcat, nest, render, empty)


import qualified Language.Haskell.Exts.Simple.Syntax as Exts
import qualified Language.Haskell.Exts.Pretty as ExtsPretty
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
    deriving (Eq, Ord, Show)
data Type = TVar Tyvar | TCon Tycon | TAp Type Type | TGen Int
    deriving (Eq, Ord, Show)
data Tyvar = Tyvar Id Kind
    deriving (Eq, Ord, Show)
data Tycon = Tycon Id Kind
    deriving (Eq, Ord, Show)

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

--merge :: Subst -> Subst -> ErrT Subst
--merge s s' =
--    if agree
--    then return (s ++ s')
--    else throwE $ text "Merge fails" -- TODO: Could show where substs disagree
--    where
--        agree = all subsEqual tvInter
--        subsEqual = \u -> apply s (TVar u) == apply s' (TVar u)
--        tvInter = map fst s `intersect` map fst s'


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
mgu t s = throwE $ capIndent
    "Types do not unify:"
    [ typeDoc "t" t
    , typeDoc "s" s
    ]

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

-- SECTION 8 (Type Schemes)
--
--  This is modified and doesn't use qualified types, since
--  we also do not use predicates (no type classes)
--------------------------------------------------------------
--------------------------------------------------------------

data Scheme = Forall [Kind] Type deriving (Eq, Ord, Show)

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

data Assump = Id :>: Scheme deriving (Eq, Ord, Show)

instance Types Assump where
    apply s (i :>: sc) = i :>: (apply s sc)
    tv (i :>: sc) = tv sc
    
schemeFromAssumps :: Id -> [Assump] -> ErrT Scheme
schemeFromAssumps i [] = throwE $ text $ "Unbound identifier: " ++ i
schemeFromAssumps i ((i' :>: sc) : as) = 
    if i == i' then return sc else schemeFromAssumps i as

-- DEBUG VERSION
--schemeFromAssumps :: Id -> [Assump] -> ErrT Scheme
--schemeFromAssumps i as = schemeFromAssumps' i as as
--
--schemeFromAssumps' :: Id -> [Assump] -> [Assump] -> ErrT Scheme
--schemeFromAssumps' i [] org = throwE $ indent
--    (text $ "Unbound identifier " ++ i)
--    (text $ "Assumps: " ++ (show $ map prettyAssump' org))
--schemeFromAssumps' i ((i' :>: sc) : as) org = 
--    if i == i' then return sc else schemeFromAssumps' i as org

assumpName :: Assump -> Id
assumpName (i :>: _) = i

hasName :: Id -> Assump -> Bool
hasName i (j :>: _) = i == j

nameEq :: Assump -> Assump -> Bool
nameEq (i :>: _) (j :>: _) = i == j

-- SECTION 10 (Type Inference Monad)
--------------------------------------------------------------
--------------------------------------------------------------

-- Tuple type representing the state
--  (current sub, fresh var, error context stack)
type TIState = (Subst, Int, [Doc])
nullTIState :: TIState
nullTIState = (nullSubst, 0, [])

type TI = StateT TIState ErrT
    
runTI :: TI a -> Err a
runTI f = runExcept $ evalStateT f nullTIState

getSubst :: TI Subst
getSubst = gets $ \(s, _, _) -> s

withErrorContexts :: [Doc] -> TI a -> TI a
withErrorContexts errs ti = do
    es <- getErrorContexts
    addErrorContexts errs
    res <- ti
    restoreErrorContextStack es
    return res
    where
        addErrorContexts :: [Doc] -> TI ()
        addErrorContexts errs = modify $ 
            \(s, n, es) -> (s, n, es ++ errs)

        restoreErrorContextStack :: [Doc] -> TI ()
        restoreErrorContextStack es = modify $
            \(s, n, _) -> (s, n, es)

withErrorContext :: Doc -> TI a -> TI a
withErrorContext err = withErrorContexts [err]

getErrorContexts :: TI [Doc]
getErrorContexts = gets $ \(_, _, es) -> es

contextsDoc :: [Doc] -> Doc
contextsDoc es = foldr (\e doc -> indent e doc) empty es

liftWithContexts :: ErrT a -> TI a
liftWithContexts action = do
    es <- getErrorContexts
    lift $ withExcept (\e -> contextsDoc $ es ++ [e]) action

unify :: Type -> Type -> TI ()
unify t t' = do
    s <- getSubst
    withErrorContext (expectedActualDoc s) $ do
        u <- liftWithContexts $ mgu (apply s t) (apply s t')
        extSubst u
    where
        expectedActualDoc s = capIndent
            "While unifying:"
            [ typeDoc "expected" $ apply s t
            , typeDoc "actual" $ apply s t'
            ]

        extSubst :: Subst -> TI ()
        extSubst s' = modify $ \(s, n, es) -> (s' @@ s, n, es)
    
newTVar :: Kind -> TI Type
newTVar k = do
    (s, n, es) <- get
    put (s, n + 1, es)
    return $ TVar $ Tyvar (enumId n) k

newVarAssump :: Id -> TI Assump
newVarAssump x = do
    v <- newTVar Star
    return $ x :>: toScheme v

freshInst :: Scheme -> TI Type
freshInst (Forall ks t) = do
    ts <- mapM newTVar ks
    return (inst ts t)

schemeInstsAreUnifiable :: Scheme -> Scheme -> Bool
schemeInstsAreUnifiable sc sc' = case runTI tryUnify of
    Left _ -> False
    Right _ -> True
    where
        tryUnify :: TI ()
        tryUnify = do
            t <- freshInst sc
            t' <- freshInst sc'
            unify t t'

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
    deriving (Eq, Ord, Show)
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
tiPat p@(PCon conA@(i :>: sc) pats) = withErrorContext errContext $ do
    -- Check if the right amount of
    -- argument patterns were provided
    t <- freshInst sc
    let expArgs = length (fst (decomposeFuncType t))
        actArgs = length pats
    if expArgs /= actArgs
    then liftWithContexts $ throwE $ errWrongArgNumber expArgs actArgs
    else do
        -- Check if types agree
        (as, ts) <- tiPats pats
        t' <- newTVar Star
        unify t (foldr fn t' ts)
        return (as, t')
    where
        errContext = capIndent
            "While inferring the type of a constructor pattern:"
            [patDoc "p" p, assumpDoc conA]

        errWrongArgNumber exp act =
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

-- Identifier
tiIdentifier :: Infer Id Type
tiIdentifier as x = do
    sc <- liftWithContexts $ schemeFromAssumps x as
    freshInst sc

tiRawTerm :: Infer CT.RawTerm Type

-- Literals
tiRawTerm as (CT.Literal l) = tiLit l
    where
        -- See unparesLiteral in Term.hs, add support for Prim Variants
        tiLit (Exts.Char _) = return tChar
        tiLit (Exts.String _) = return tString
        tiLit (Exts.Int _) = return tInt
        tiLit (Exts.Frac _) = return tFrac
        tiLit l = liftWithContexts $ throwE $ text $ concat
            ["Unsupported literal: ", show l]

-- Free, Schematic, Const
tiRawTerm as (CT.Free x) = tiIdentifier as x
tiRawTerm as (CT.Schematic x) = tiIdentifier as x
tiRawTerm as (CT.Const x) = tiIdentifier as x

-- Application
tiRawTerm as (CT.Application e f) = do
    te <- tiRawTerm as e
    tf <- tiRawTerm as f
    t <- newTVar Star
    unify (tf `fn` t) te
    return t

-- Code duplication: Use Generics!
-- Don't want to use the fixes info here (i.e. (x, n)), because that is
-- proof specific and shouldn't leak into typechecking
tiTerm' :: Infer CT.Term Type
tiTerm' as (CT.Literal l) = tiRawTerm as (CT.Literal l)
tiTerm' as (CT.Free (x, _)) = tiRawTerm as (CT.Free x)
tiTerm' as (CT.Schematic (x, _)) = tiRawTerm as (CT.Schematic x)
tiTerm' as (CT.Const s) = tiRawTerm as (CT.Const s)
tiTerm' as term@(CT.Application e f) = do
    te <- tiTerm' as e
    tf <- tiTerm' as f
    t <- newTVar Star
    unify (tf `fn` t) te
    return t

-- This is to not have a recursive error context
-- stack on repeated invocatinos of tiTerm App
tiTerm :: Infer CT.Term Type
tiTerm as term = withErrorContext errContext $
    tiTerm' as term
    where
        errContext = capIndent
            "While inferring the type of the term:"
            [CT.unparseTermPretty term]



-- Type inference for Alts
---------------------------------

type Alt = ([Pat], CT.Term)

tiAlt :: Infer Alt Type
tiAlt as alt@(pats, term) = withErrorContext errContext $ do
    (as', ts) <- tiPats pats
    t <- tiTerm (as' ++ as) term
    return $ foldr fn t ts
    where
        errContext = capIndent
            "While inferring the function (represented by <f>) alternative type"
            [altDocWithName "<f>" alt]
        

tiAlts :: [Assump] -> [Alt] -> Type -> TI ()
tiAlts as alts t = withErrorContext errContextOuter $ do
    ts <- mapM (tiAlt as) alts
    mapM_ checkAlt $ zip ts alts
    where
        errContextOuter = capIndent
            "While typechecking the function (represented by <f>) alternatives"
            [ typeDoc "Expected type" t
            , capIndent "Alternatives:" $ map (altDocWithName "<f>") alts
            ]

        errContextInner alt = capIndent
            "While typechecking the function (represented by <f>) alternative"
            [altDocWithName "<f>" alt]

        checkAlt (tAlt, alt) = withErrorContext 
            (errContextInner alt) $ unify t tAlt


-- TYPE INFERENCE FOR BINDINGS
--------------------------------------------------------------------
--------------------------------------------------------------------

-- Explicit Bindings (with type signature)
---------------------------------------------------------
type ExplicitBinding = (Assump, [Alt])

tiExplBind :: [Assump] -> ExplicitBinding -> TI ()
tiExplBind as (sig@(i :>: sc), alts) = withErrorContext errContext $ do
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
    --then lift $ throwE $ errMsg (i :>: sc') sig
    then liftWithContexts $ throwE $ errMsg (i :>: sc') sig
    else return ()
    where
        -- Add type signature to assumptions
        as' = sig : as

        errContext = hsep $ map text
            [ "While checking the type of the explicit binding"
            , prettyAssump' sig
            ]

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
tiImplBinds as binds = withErrorContext errContext $ do
    -- Make new tvars and assumptions about
    -- those tvars (to support polymorphic
    -- recursions) for all binds
    funTypes <- replicateM (length binds) $ newTVar Star
    let ids = map fst binds
        scs = map toScheme funTypes
        as' = (zipWith (:>:) ids scs) ++ as
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
    where
        errContext = hsep $ map text
            [ "While inferring the types of the implicit bindings"
            , concat $ intersperse ", " $ map fst binds
            ]

-- Bind Groups
---------------------------------------------------------
type BindGroup = ([ExplicitBinding], [[ImplicitBinding]])

tiBindGroup :: Infer BindGroup [Assump]
tiBindGroup as (expls, implGroups) = do
    asImpls <- tiSeq tiImplBinds (asExpls ++ as) implGroups
    mapM (tiExplBind (asImpls ++ asExpls ++ as)) expls
    return (asImpls ++ asExpls)
    where
        -- Type signature assumptions, to be
        -- used while inferring impls
        asExpls = map fst expls

-- Sequences type inference actions, passing assumptions
-- generated by one action to the next
tiSeq :: Infer bg [Assump] -> Infer [bg] [Assump]
tiSeq ti as [] = return []
tiSeq ti as (group : rest) = do
    as' <- ti as group
    as'' <- tiSeq ti (as' ++ as) rest
    return (as'' ++ as')

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
prettyPat (PCon (c :>: _) ps) = if null ps
    then c
    else concat [ "(", conStr, ")"]
    where
        conStr = intercalate " " $ c : (map prettyPat ps)

-- Alt
------------------------------------------------
prettyAlt :: Alt -> String
prettyAlt (lhs, rhs) = concat
    [ intercalate " " $ map prettyPat lhs
    , " = "
    , render $ CT.unparseTermPretty rhs
    ]

prettyAlts :: [Alt] -> String
prettyAlts alts = concat
    [ "[ "
    , intercalate " " $ map prettyAlt alts
    , " ]"
    ]

-- Bindings
------------------------------------------------
prettyExplicitBinding :: ExplicitBinding -> String
prettyExplicitBinding (sig, alts) = concat
    [ "sig = "
    , prettyAssump' sig
    , ", alts = "
    , prettyAlts alts
    ]

prettyImplicitBinding :: ImplicitBinding -> String
prettyImplicitBinding (id, alts) = concat
    [ "name = "
    , id
    , ", alts = "
    , prettyAlts alts
    ]

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

termDoc :: String -> CT.Term -> Doc
termDoc name t = eqDoc name $ render $ CT.unparseTermPretty t

altDocWithName :: String -> Alt -> Doc
altDocWithName f alt = hsep $ map text [f, prettyAlt alt]

capIndent :: String -> [Doc] -> Doc
capIndent cap docs = indent (text cap) $ vcat docs
