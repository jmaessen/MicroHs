-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module MicroHs.Ident(
  Line, Col, Loc,
  Ident(..),
  mkIdent, mkIdentLoc, unIdent, eqIdent, leIdent, isIdent,
  qualIdent, showIdent, getSLocIdent, setSLocIdent,
  ppIdent,
  mkIdentSLoc,
  isLower_, isIdentChar, isOperChar, isConIdent,
  dummyIdent, isDummyIdent,
  unQualIdent,
  unQualString,
  addIdentSuffix,
  SLoc(..), noSLoc, isNoSLoc,
  showSLoc,
  compareIdent,
  ) where
import Data.Eq
import Prelude --Xhiding(showString)
import Data.Char
import Text.PrettyPrint.HughesPJ
--Ximport Control.DeepSeq
--Yimport Primitives(NFData(..))
--Ximport Compat
--Ximport GHC.Stack

type Line = Int
type Col  = Int
type Loc  = (Line, Col)

data SLoc = SLoc FilePath Line Col
  --Xderiving (Show, Eq)

data Ident = Ident SLoc String
  --Xderiving (Show)
--Winstance NFData Ident where rnf (Ident _ s) = rnf s

instance Eq Ident where
  Ident _ i == Ident _ j  =  i == j

noSLoc :: SLoc
noSLoc = SLoc "" 0 0

isNoSLoc :: SLoc -> Bool
isNoSLoc (SLoc _ 0 0) = True
isNoSLoc _ = False

mkIdent :: String -> Ident
mkIdent = Ident noSLoc

mkIdentSLoc :: SLoc -> String -> Ident
mkIdentSLoc = Ident

mkIdentLoc :: FilePath -> Loc -> String -> Ident
mkIdentLoc fn (l, c) s = Ident (SLoc fn l c) s

unIdent :: Ident -> String
unIdent (Ident _ s) = s

getSLocIdent :: Ident -> SLoc
getSLocIdent (Ident loc _) = loc

setSLocIdent :: SLoc -> Ident -> Ident
setSLocIdent l (Ident _ s) = Ident l s

showIdent :: Ident -> String
showIdent (Ident _ i) = i

ppIdent :: Ident -> Doc
ppIdent (Ident _ i) = text i

isIdent :: String -> Ident -> Bool
isIdent s (Ident _ i) = s == i

leIdent :: Ident -> Ident -> Bool
leIdent (Ident _ i) (Ident _ j) = leString i j

eqIdent :: Ident -> Ident -> Bool
eqIdent (Ident _ i) (Ident _ j) = eqString i j

qualIdent :: Ident -> Ident -> Ident
qualIdent (Ident loc qi) (Ident _ i) = Ident loc (qi ++ "." ++ i)

addIdentSuffix :: Ident -> String -> Ident
addIdentSuffix (Ident loc i) s = Ident loc (i ++ s)

unQualString :: --XHasCallStack =>
                String -> String
unQualString [] = ""
unQualString s@(c:_) =
  if isIdentChar c then
    case dropWhile (neChar '.') s of
      "" -> s
      '.':r -> unQualString r
      _ -> undefined -- This cannot happen, but GHC doesn't know that
  else
    s

unQualIdent :: Ident -> Ident
unQualIdent (Ident l s) = Ident l (unQualString s)

isConIdent :: Ident -> Bool
isConIdent (Ident _ i) =
  let
    c = head i
  in isUpper c || c == ':' || c == ',' || i == "[]"  || i == "()"

isOperChar :: Char -> Bool
isOperChar c = elem c "@\\=+-:<>.!#$%^&*/|~?"

isIdentChar :: Char -> Bool
isIdentChar c = isLower_ c || isUpper c || isDigit c || c == '\''

isLower_ :: Char -> Bool
isLower_ c = isLower c || c == '_'

dummyIdent :: Ident
dummyIdent = mkIdent "_"

isDummyIdent :: Ident -> Bool
isDummyIdent (Ident _ "_") = True
isDummyIdent _ = False

showSLoc :: SLoc -> String
showSLoc (SLoc fn l c) =
  if null fn then "no location" else
  showString fn ++ ": " ++ "line " ++ showInt l ++ ", col " ++ showInt c

compareIdent :: Ident -> Ident -> Ordering
compareIdent (Ident _ s) (Ident _ t) = compareString s t


