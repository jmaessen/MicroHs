module MicroHs.Expr(
  IdentModule,
  EModule(..),
  ExportItem(..),
  ImportSpec(..),
  ImportItem(..),
  EDef(..), showEDefs,
  Expr(..), showExpr,
  Listish(..),
  Lit(..), showLit, eqLit,
  EBind(..), showEBind,
  Eqn(..),
  EStmt(..),
  EAlts(..),
  EAlt,
  ECaseArm,
  EType, showEType, eqEType,
  EConstraint,
  EPat, patVars, isPVar, isPConApp,
  EKind, kType, kConstraint,
  IdKind(..), idKindIdent,
  LHS,
  Constr(..), ConstrField,
  ConTyInfo,
  Con(..), conIdent, conArity, eqCon, getSLocCon,
  tupleConstr, untupleConstr, isTupleConstr,
  subst,
  allVarsExpr, allVarsBind,
  getSLocExpr, setSLocExpr,
  getSLocEqns,
  errorMessage,
  Assoc(..), eqAssoc, Fixity
  ) where
import Prelude --Xhiding (Monad(..), Applicative(..), MonadFail(..), Functor(..), (<$>), showString, showChar, showList, (<>))
import Data.Maybe
import MicroHs.Ident
import qualified Data.Double as D
--Ximport Compat
--Ximport GHC.Stack
--Ximport Control.DeepSeq
--Yimport Primitives(NFData(..))
import MicroHs.Pretty

type IdentModule = Ident

----------------------

data EModule = EModule IdentModule [ExportItem] [EDef]
  --Xderiving (Show, Eq)

data ExportItem
  = ExpModule IdentModule
  | ExpTypeCon Ident
  | ExpType Ident
  | ExpValue Ident
  --Xderiving (Show, Eq)

data EDef
  = Data LHS [Constr]
  | Newtype LHS Constr
  | Type LHS EType
  | Fcn Ident [Eqn]
  | Sign Ident EType
  | Import ImportSpec
  | ForImp String Ident EType
  | Infix Fixity [Ident]
  | Class [EConstraint] LHS [EBind]  -- XXX will probable need initial forall with FD
  | Instance [IdKind] [EConstraint] EConstraint [EBind]  -- no deriving yet
  --Xderiving (Show, Eq)

data ImportSpec = ImportSpec Bool Ident (Maybe Ident) (Maybe (Bool, [ImportItem]))  -- first Bool indicates 'qualified', second 'hiding'
  --Xderiving (Show, Eq)

data ImportItem
  = ImpTypeCon Ident
  | ImpType Ident
  | ImpValue Ident
  --Xderiving (Show, Eq)

data Expr
  = EVar Ident
  | EApp Expr Expr
  | EOper Expr [(Ident, Expr)]
  | ELam [EPat] Expr
  | ELit SLoc Lit
  | ECase Expr [ECaseArm]
  | ELet [EBind] Expr
  | ETuple [Expr]
  | EListish Listish
  | EDo (Maybe Ident) [EStmt]
  | ESectL Expr Ident
  | ESectR Ident Expr
  | EIf Expr Expr Expr
  | ESign Expr EType
  | EAt Ident Expr  -- only in patterns
  -- Only while type checking
  | EUVar Int
  -- Constructors after type checking
  | ECon Con
  | EForall [IdKind] Expr -- only in types
  --Xderiving (Show, Eq)

data Con
  = ConData ConTyInfo Ident
  | ConNew Ident
  | ConLit Lit
--  | ConTup Int
  --Xderiving(Show, Eq)

data Listish
  = LList [Expr]
  | LCompr Expr [EStmt]
  | LFrom Expr
  | LFromTo Expr Expr
  | LFromThen Expr Expr
  | LFromThenTo Expr Expr Expr
  --Xderiving(Show, Eq)

conIdent :: --XHasCallStack =>
            Con -> Ident
conIdent (ConData _ i) = i
conIdent (ConNew i) = i
conIdent _ = error "conIdent"

conArity :: Con -> Int
conArity (ConData cs i) = fromMaybe (error "conArity") $ lookupBy eqIdent i cs
conArity (ConNew _) = 1
conArity (ConLit _) = 0

eqCon :: Con -> Con -> Bool
eqCon (ConData _ i) (ConData _ j) = eqIdent i j
eqCon (ConNew    i) (ConNew    j) = eqIdent i j
eqCon (ConLit    l) (ConLit    k) = eqLit   l k
eqCon _             _             = False

data Lit
  = LInt Int
  | LDouble D.Double
  | LChar Char
  | LStr String
  | LPrim String
  | LForImp String
  --Xderiving (Show, Eq)
--Winstance NFData Lit where rnf (LInt i) = rnf i; rnf (LDouble d) = rnf d; rnf (LChar c) = rnf c; rnf (LStr s) = rnf s; rnf (LPrim s) = rnf s; rnf (LForImp s) = rnf s

eqLit :: Lit -> Lit -> Bool
eqLit (LInt x)  (LInt  y) = x == y
eqLit (LChar x) (LChar y) = eqChar x y
eqLit (LStr  x) (LStr  y) = eqString x y
eqLit (LPrim x) (LPrim y) = eqString x y
eqLit (LForImp x) (LForImp y) = eqString x y
eqLit _         _         = False

type ECaseArm = (EPat, EAlts)

data EStmt = SBind EPat Expr | SThen Expr | SLet [EBind]
  --Xderiving (Show, Eq)

data EBind = BFcn Ident [Eqn] | BPat EPat Expr | BSign Ident EType
  --Xderiving (Show, Eq)

-- A single equation for a function
data Eqn = Eqn [EPat] EAlts
  --Xderiving (Show, Eq)

data EAlts = EAlts [EAlt] [EBind]
  --Xderiving (Show, Eq)

type EAlt = ([EStmt], Expr)

type ConTyInfo = [(Ident, Int)]    -- All constructors with their arities

type EPat = Expr

isPVar :: EPat -> Bool
isPVar (EVar i) = not (isConIdent i)
isPVar _ = False    

isPConApp :: EPat -> Bool
isPConApp (EVar i) = isConIdent i
isPConApp (EApp f _) = isPConApp f
isPConApp _ = True

patVars :: EPat -> [Ident]
patVars = filter isVar . allVarsExpr
  where isVar v = not (isConIdent v) && not (isDummyIdent v)

type LHS = (Ident, [IdKind])

data Constr = Constr Ident (Either [EType] [ConstrField])
  --Xderiving(Show, Eq)

type ConstrField = (Ident, EType)              -- record label and type

-- Expr restricted to
--  * after desugaring: EApp and EVar
--  * before desugaring: EApp, EVar, ETuple, EList
type EType = Expr

type EConstraint = EType

data IdKind = IdKind Ident EKind
  --Xderiving (Show, Eq)

idKindIdent :: IdKind -> Ident
idKindIdent (IdKind i _) = i

type EKind = EType

kType :: EKind
kType = EVar (Ident noSLoc "Primitives.Type")

kConstraint :: EKind
kConstraint = EVar (Ident noSLoc "Primitives.Constraint")

tupleConstr :: SLoc -> Int -> Ident
tupleConstr loc n = mkIdentSLoc loc (replicate (n - 1) ',')

untupleConstr :: Ident -> Int
untupleConstr i = length (unIdent i) + 1

isTupleConstr :: Int -> Ident -> Bool
isTupleConstr n i = eqChar (head (unIdent i)) ',' && untupleConstr i == n

---------------------------------

data Assoc = AssocLeft | AssocRight | AssocNone
  --Xderiving (Eq, Show)

eqAssoc :: Assoc -> Assoc -> Bool
eqAssoc AssocLeft AssocLeft = True
eqAssoc AssocRight AssocRight = True
eqAssoc AssocNone AssocNone = True
eqAssoc _ _ = False

type Fixity = (Assoc, Int)

---------------------------------

-- Enough to handle subsitution in types
subst :: [(Ident, Expr)] -> Expr -> Expr
subst s =
  let
    sub ae =
      case ae of
        EVar i -> fromMaybe ae $ lookupBy eqIdent i s
        EApp f a -> EApp (sub f) (sub a)
        ESign e t -> ESign (sub e) t
        EUVar _ -> ae
        _ -> error "subst unimplemented"
  in sub

---------------------------------

-- XXX needs more?
eqEType :: EType -> EType -> Bool
eqEType (EVar i) (EVar i') = eqIdent i i'
eqEType (EApp f a) (EApp f' a') = eqEType f f' && eqEType a a'
eqEType _ _ = False

---------------------------------

allVarsBind :: EBind -> [Ident]
allVarsBind abind =
  case abind of
    BFcn i eqns -> i : concatMap allVarsEqn eqns
    BPat p e -> allVarsPat p ++ allVarsExpr e
    BSign i _ -> [i]

allVarsEqn :: Eqn -> [Ident]
allVarsEqn eqn =
  case eqn of
    Eqn ps alts -> concatMap allVarsPat ps ++ allVarsAlts alts

allVarsAlts :: EAlts -> [Ident]
allVarsAlts (EAlts alts bs) = concatMap allVarsAlt alts ++ concatMap allVarsBind bs

allVarsAlt :: EAlt -> [Ident]
allVarsAlt (ss, e) = concatMap allVarsStmt ss ++ allVarsExpr e

allVarsPat :: EPat -> [Ident]
allVarsPat = allVarsExpr

allVarsExpr :: Expr -> [Ident]
allVarsExpr aexpr =
  case aexpr of
    EVar i -> [i]
    EApp e1 e2 -> allVarsExpr e1 ++ allVarsExpr e2
    EOper e1 ies -> allVarsExpr e1 ++ concatMap (\ (i,e2) -> i : allVarsExpr e2) ies
    ELam ps e -> concatMap allVarsPat ps ++ allVarsExpr e
    ELit _ _ -> []
    ECase e as -> allVarsExpr e ++ concatMap allVarsCaseArm as
    ELet bs e -> concatMap allVarsBind bs ++ allVarsExpr e
    ETuple es -> concatMap allVarsExpr es
    EListish (LList es) -> concatMap allVarsExpr es
    EDo mi ss -> maybe [] (:[]) mi ++ concatMap allVarsStmt ss
    ESectL e i -> i : allVarsExpr e
    ESectR i e -> i : allVarsExpr e
    EIf e1 e2 e3 -> allVarsExpr e1 ++ allVarsExpr e2 ++ allVarsExpr e3
    EListish l -> allVarsListish l
    ESign e _ -> allVarsExpr e
    EAt i e -> i : allVarsExpr e
    EUVar _ -> []
    ECon c -> [conIdent c]
    EForall iks e -> map (\ (IdKind i _) -> i) iks ++ allVarsExpr e

allVarsListish :: Listish -> [Ident]
allVarsListish (LList es) = concatMap allVarsExpr es
allVarsListish (LCompr e ss) = allVarsExpr e ++ concatMap allVarsStmt ss
allVarsListish (LFrom e) = allVarsExpr e
allVarsListish (LFromTo e1 e2) = allVarsExpr e1 ++ allVarsExpr e2
allVarsListish (LFromThen e1 e2) = allVarsExpr e1 ++ allVarsExpr e2
allVarsListish (LFromThenTo e1 e2 e3) = allVarsExpr e1 ++ allVarsExpr e2 ++ allVarsExpr e3

allVarsCaseArm :: ECaseArm -> [Ident]
allVarsCaseArm (p, alts) = allVarsPat p ++ allVarsAlts alts

allVarsStmt :: EStmt -> [Ident]
allVarsStmt astmt =
  case astmt of
    SBind p e -> allVarsPat p ++ allVarsExpr e
    SThen e -> allVarsExpr e
    SLet bs -> concatMap allVarsBind bs

-----------------------------

-- XXX Should use locations in ELit
getSLocExpr :: Expr -> SLoc
getSLocExpr e = head $ filter (not . isNoSLoc) (map getSLocIdent (allVarsExpr e)) ++ [noSLoc]

getSLocEqns :: [Eqn] -> SLoc
getSLocEqns eqns = getSLocExpr $ ELet [BFcn dummyIdent eqns] (EVar dummyIdent)

getSLocCon :: Con -> SLoc
getSLocCon (ConData _ i) = getSLocIdent i
getSLocCon (ConNew i) = getSLocIdent i
getSLocCon _ = noSLoc

setSLocExpr :: SLoc -> Expr -> Expr
setSLocExpr l (EVar i) = EVar (setSLocIdent l i)
setSLocExpr l (ECon c) = ECon (setSLocCon l c)
setSLocExpr l (ELit _ k) = ELit l k
setSLocExpr _ _ = error "setSLocExpr"  -- what other cases do we need?

setSLocCon :: SLoc -> Con -> Con
setSLocCon l (ConData ti i) = ConData ti (setSLocIdent l i)
setSLocCon l (ConNew i) = ConNew (setSLocIdent l i)
setSLocCon _ c = c

errorMessage :: --XHasCallStack =>
                forall a . SLoc -> String -> a
errorMessage loc msg = error $ showSLoc loc ++ ": " ++ msg

----------------

