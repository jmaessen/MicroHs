module MicroHs.HashCons(hashCons) where
import Prelude
import Data.Maybe(fromMaybe)
import MicroHs.Desugar(LDef)
import MicroHs.Exp(Exp(..))
import MicroHs.Expr(Lit, showLit)
import MicroHs.Ident(Ident, mkIdent)
import qualified MicroHs.IntMap as IM
import MicroHs.State
import qualified MicroHs.IdentMap as M

type Node = Int

data GExp
  = GApp Node Node
  | GVar Ident
  | GLit Lit

data Graph = Graph {
    n :: Node,  -- Next unused node
    nodes :: IM.IntMap GExp,
    apps :: PairMap Node,
    vars :: M.Map Node,
    lits :: M.Map Node
  }

type M a = State Graph a

type PairMap v = IM.IntMap (IM.IntMap v)

lookupPM :: Int -> Int -> PairMap v -> Maybe v
lookupPM a b m = IM.lookup b =<< IM.lookup a m

insertPM :: Int -> Int -> v -> PairMap v -> PairMap v
insertPM a b v m = IM.insert a (IM.insert b v ma) m
  where ma = fromMaybe IM.empty (IM.lookup a m)

newNode :: GExp -> M Node
newNode ge = do
  s <- get
  let cn = n s
      nn = cn + 1
  put $ s{ n = nn, nodes = IM.insert cn ge (nodes s) }
  modify (nodeUpd ge cn)
  return cn

-- This is a total hack to get things off the ground.
litKey :: Lit -> Ident
litKey = mkIdent . showLit

nodeUpd :: GExp -> Node -> Graph -> Graph
nodeUpd (GApp a b) n s =
  s{ apps = insertPM a b n (apps s) }
nodeUpd (GVar v) n s =
  s{ vars = M.insert v n (vars s) }
nodeUpd (GLit l) n s =
  s{ vars = M.insert (litKey l) n (lits s) }

getNode :: GExp -> M (Maybe Node)
getNode ge = fmap (getNodeG ge) get

getNodeG :: GExp -> Graph -> Maybe Node
getNodeG (GApp a b) s =
  lookupPM a b (apps s)
getNodeG (GVar v) s =
  M.lookup v (vars s)
getNodeG (GLit l) s =
  M.lookup (litKey l) (lits s)

node :: GExp -> M Node
node ge = do
  mh <- getNode ge
  case mh of
    Just n -> return n
    Nothing -> newNode ge

nodeForExp :: Exp -> M Node
nodeForExp (App a b) = do
  a' <- nodeForExp a
  b' <- nodeForExp b
  node (GApp a' b')
nodeForExp (Var v) =
  node (GVar v)
nodeForExp (Lit l) =
  node (GLit l)
nodeForExp (Lam _ _) = error "nodeForExp Lam"

type Roots = IM.IntMap Ident

expForNode :: Roots -> Node -> M Exp
expForNode rs n =
  case IM.lookup n rs of
    Just v -> return $ Var v
    Nothing -> expForRoot rs n

expForRoot :: Roots -> Node -> M Exp
expForRoot rs n = gets (\s -> nodes s IM.! n) >>= expForGExp rs

expForGExp :: Roots -> GExp -> M Exp
expForGExp _ (GVar v) = return $ Var v
expForGExp _ (GLit l) = return $ Lit l
expForGExp rs (GApp a b) = App <$> expForNode rs a <*> expForNode rs b

-- Returns count of uses of shared app nodes (>1)
sharedApps :: Graph -> IM.IntMap Int
sharedApps g =
  let uses =
        [v | (a, bs) <- IM.toList $ apps g,
             b <- IM.keys bs,
             v <- [a,b],
             Just (GApp _ _) <- [IM.lookup v (nodes g)] ]
  in IM.filter (1<) $ foldr (\k -> IM.insertWith (+) k 1) IM.empty uses

hashCons :: [LDef] -> [LDef]
hashCons ds =
  let g0 = Graph {
        n = 0,
        nodes = IM.empty,
        apps = IM.empty,
        vars = M.empty,
        lits = M.empty
      }
  in evalState (hashConsM ds) g0

nodeKey :: Node -> Ident
nodeKey n = mkIdent ("!nd"++show n)

hashConsM :: [LDef] -> M [LDef]
hashConsM ds = do
  ds' <- mapM (\(i, e) -> (i,) <$> nodeForExp e) ds
  shared <- gets sharedApps
  let roots = IM.fromList (
        [(n, nodeKey n) | (n, _) <- IM.toList shared]
        ++ [(n, v) | (v, n) <- ds'])
      trivs = [(i, v) | (i, v@(Var _)) <- ds]
  (++trivs) <$> (mapM (\(n, v) -> (v,) <$> expForRoot roots n) $ IM.toList roots)
