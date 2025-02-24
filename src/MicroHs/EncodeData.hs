{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module MicroHs.EncodeData(
  SPat(..),
  encConstr,
  encCase,
  encIf,
  encList,
  ) where
import Prelude
import MicroHs.Exp
import MicroHs.Expr(Con(..), Lit(..))
import MicroHs.Ident
import Compat

--
-- Encoding of constructors and case
--

data SPat = SPat Con [Ident]    -- simple pattern
--  deriving(Show, Eq)

encCase :: Exp -> [(SPat, Exp)] -> Exp -> Exp
encCase var pes dflt | n <= scottLimit = encCaseScott var pes dflt
                     | otherwise = encCaseNo var pes dflt
  where n = numConstr pes

encConstr :: Int -> Int -> [Bool] -> Exp
encConstr i n ss | n /= n = undefined  -- XXX without this, everything slows down.  Why?
                 | n <= scottLimit = encConstrScott i n ss
                 | otherwise       = encConstrNo i n ss

encIf :: Exp -> Exp -> Exp -> Exp
encIf = encIfScott

-- Lowest value that works is 3.
-- The runtime system knows the encoding of some types:
-- Bool, [], Ordering
scottLimit :: Int
scottLimit = 5

-------------------------------------------

-- Scott encoding
--   C_i e1 ... en
-- encodes as, assuming k constructors
--   \ x1 ... xn -> \ f1 ... fi ... fk -> fi x1 ... xn

-- Encode a case expression:
--  case var of p1->e1; p2->e2; ...; _->dflt
encCaseScott :: Exp -> [(SPat, Exp)] -> Exp -> Exp
encCaseScott var pes dflt =
  --trace ("mkCase " ++ show pes) $
  case pes of
    (SPat (ConData cs _ _) _, _) : _ ->
      let
        arm (c, k) =
          let
            (vs, rhs) = head $ [ (xs, e) | (SPat (ConData _ i _) xs, e) <- pes, c == i ] ++
                               [ (replicate k dummyIdent, dflt) ]
          in lams vs rhs
      in  apps var (map arm cs)
    _ -> undefined

-- Encode a constructor with strictness flags ss.
-- The constructor arity is given by ss, and the constructor number is i out of n.
encConstrScott :: Int -> Int -> [Bool] -> Exp
encConstrScott i n ss =
  let
    f = mkIdent "$f"
    fs = map (\ k -> if k == i then f else dummyIdent) [0::Int .. n-1]
    xs = [mkIdent ("$x" ++ show j) | (j, _) <- zip [0::Int ..] ss]
    strict (False:ys) (_:is) e = strict ys is e
    strict (True:ys)  (x:is) e = App (App (Lit (LPrim "seq")) (Var x)) (strict ys is e)
    strict _ _ e = e
  in lams xs $ strict ss xs $ lams fs $ apps (Var f) (map Var xs)  

encIfScott :: Exp -> Exp -> Exp -> Exp
encIfScott c t e = app2 c e t

encList :: [Exp] -> Exp
encList = foldr (app2 cCons) cNil

-- XXX could use encConstr
cCons :: Exp
cCons = Lit (LPrim "O")

-- XXX could use encConstr
cNil :: Exp
cNil = Lit (LPrim "K")

-------------------------------------------

-- Explicit constructor number encoding
--   C_i e1 e2 ... en
-- encodes as
--   (i, (e1, e2, ..., en))
-- with the tuples being Scott encoded.

-- Could be improved by a new node type holding
-- both the constructor number and a pointer to the tuple.
-- Also, could use a "jump table" case combinator instead
-- of a decision tree.

encConstrNo :: Int -> Int -> [Bool] -> Exp
encConstrNo i _n ss =
  let
    xs = [mkIdent ("$x" ++ show j) | (j, _) <- zip [0::Int ..] ss]
    strict (False:ys) (_:is) e = strict ys is e
    strict (True:ys)  (x:is) e = App (App (Lit (LPrim "seq")) (Var x)) (strict ys is e)
    strict _ _ e = e
  in lams xs $ strict ss xs $ tuple [Lit (LInt i), tuple (map Var xs)]

tuple :: [Exp] -> Exp
tuple es = Lam f $ apps (Var f) es
  where f = -- newIdent "$t" es --
            mkIdent "$t"
  
encCaseNo :: Exp -> [(SPat, Exp)] -> Exp -> Exp
encCaseNo var pes dflt =
  App var (Lam n $ Lam t $ caseTree (Var n) (Var t) 0 (numConstr pes) pes' dflt)
  where n = -- newIdent "$n" es --
            mkIdent "$n"
        t = -- newIdent "$tt" es --
            mkIdent "$tt"
        --es = var : dflt : map snd pes
        pes' = sortLE (\ (x, _, _) (y, _, _) -> x <= y)
                      [(conNo c, xs, e) | (SPat c xs, e) <- pes]

caseTree :: Exp -> Exp -> Int -> Int -> [(Int, [Ident], Exp)] -> Exp -> Exp
caseTree n tup lo hi pes dflt =
  case pes of
    [] -> dflt
    [(i, xs, e)] | hi - lo == 1 -> match tup xs e
                 | otherwise    -> encIf (eqInt n i) (match tup xs e) dflt
    _ ->
      let (pesl, pesh@((i, _, _):_)) = splitAt (length pes `quot` 2) pes
      in  encIf (ltInt n i) (caseTree n tup lo i pesl dflt) (caseTree n tup i hi pesh dflt)
 where
   eqInt :: Exp -> Int -> Exp
   eqInt x i = app2 (Lit (LPrim "==")) x (Lit (LInt i))
   ltInt :: Exp -> Int -> Exp
   ltInt x i = app2 (Lit (LPrim "<")) x (Lit (LInt i))
   match :: Exp -> [Ident] -> Exp -> Exp
   match e is rhs = App e $ lams is rhs

conNo :: Con -> Int
conNo (ConData cks i _) = length $ takeWhile ((/= i) . fst) cks
conNo _ = undefined

numConstr :: [(SPat, Exp)] -> Int
numConstr ((SPat (ConData cs _ _) _, _):_) = length cs
numConstr _ = undefined

