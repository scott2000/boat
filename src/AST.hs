module AST where

import Data.Word
import Data.List

data CompilerState = CompilerState
  { anonTypes :: Word64 }

data Position = Position
  { posLine :: Int
  , posColumn :: Int }
  deriving Eq

data Span = Span
  { spanStart :: Position
  , spanEnd :: Position }
  deriving Eq

data Meta a = Meta
  { unmeta :: a
  , metaTy :: Maybe Type
  , metaSpan :: Maybe Span }
  deriving Functor

instance Eq a => Eq (Meta a) where
  m0 == m1 = unmeta m0 == unmeta m1 && metaTy m0 == metaTy m1

instance Show a => Show (Meta a) where
  show = show . unmeta

meta :: a -> Meta a
meta x = Meta
  { unmeta = x
  , metaTy = Nothing
  , metaSpan = Nothing }

metaWithSpan :: Span -> a -> Meta a
metaWithSpan span x = (meta x)
  { metaSpan = Just span }

data TBase
  = TNamed String
  | TPoly String
  | TAnon Word64
  deriving Eq

data Type
  = TApp TBase [Meta Type]
  deriving Eq

tApp :: [Meta Type] -> Type -> Type
tApp types (TApp base xs) = TApp base (xs ++ types)

tFunc :: Meta Type -> Meta Type -> Type
tFunc a b = TApp (TNamed "Fun") [a, b]

data Value
  = VUnit
  | VFun [MatchCase]

instance Show Value where
  show = \case
    VUnit -> "()"
    VFun cases -> 
      "(fun" ++ showCases cases ++ ")"

instance Eq Value where
  VUnit == VUnit = True
  VFun c0 == VFun c1 =
    c0 == c1
  _ == _ = False

type MatchCase = ([Meta Pattern], Meta Expr)

data Expr
  = EValue Value
  | EGlobal String
  | EIndex Int (Maybe String)
  | EApp (Meta Expr) (Meta Expr)
  | ESeq (Meta Expr) (Meta Expr)
  | ELet (Meta Pattern) (Meta Expr) (Meta Expr)
  | EMatchIn [Meta Expr] [MatchCase]

instance Eq Expr where
  EValue v0 == EValue v1 =
    v0 == v1
  EGlobal n0 == EGlobal n1 =
    n0 == n1
  EIndex x0 _ == EIndex x1 _ =
    x0 == x1
  EApp a0 b0 == EApp a1 b1 =
    a0 == a1 && b0 == b1
  ESeq a0 b0 == ESeq a1 b1 =
    a0 == a1 && b0 == b1
  ELet p0 v0 e0 == ELet p1 v1 e1 =
    p0 == p1 && v0 == v1 && e0 == e1
  EMatchIn e0 c0 == EMatchIn e1 c1 =
    e0 == e1 && c0 == c1
  _ == _ = False

instance Show Expr where
  show = \case
    EValue val -> show val
    EGlobal name -> name
    EIndex 0 Nothing -> "?"
    EIndex n Nothing -> "?" ++ show n
    EIndex _ (Just name) -> name
    EApp a b ->
      "(" ++ show a ++ " " ++ show b ++ ")"
    ESeq a b ->
      "(" ++ show a ++ "; " ++ show b ++ ")"
    ELet p v e ->
      "(let " ++ show p ++ " =" ++ indent (show v) ++ "\n" ++ show e ++ ")"
    EMatchIn exprs cases ->
      "(match " ++ intercalate " " (map show exprs) ++ " in" ++ showCases cases ++ ")"

indent :: String -> String
indent = indentLines . lines
  where
    indentLines [one] = " " ++ one
    indentLines rest = "\n  " ++ intercalate "\n  " rest

showCases :: [MatchCase] -> String
showCases [c] = indent (showCase c)
showCases cases = "\n  " ++ intercalate "\n  " (map showCase cases)

showCase :: MatchCase -> String
showCase (pats, expr) = intercalate " " (map show pats) ++ " ->" ++ indent (show expr)

toDeBruijn :: Meta Expr -> Meta Expr
toDeBruijn = fmap $ \case
  EValue val ->
    EValue $ toDeBruijnVal val
  EGlobal name ->
    EGlobal name
  EIndex index _ ->
    EIndex index Nothing
  EApp a b ->
    EApp (toDeBruijn a) (toDeBruijn b)
  ESeq a b ->
    ESeq (toDeBruijn a) (toDeBruijn b)
  ELet p v e ->
    ELet (toDeBruijnPat p) (toDeBruijn v) (toDeBruijn e)
  EMatchIn exprs cases ->
    EMatchIn (map toDeBruijn exprs) $ map toDeBruijnCase cases
  where
    toDeBruijnVal = \case
      VFun cases ->
        VFun $ map toDeBruijnCase cases
      other -> other
    toDeBruijnCase (pats, expr) = (map toDeBruijnPat pats, toDeBruijn expr)
    toDeBruijnPat = fmap $ \case
      PUnit -> PUnit
      PAny -> PAny
      PBind _ -> PBind Nothing
      PCons name pats ->
        PCons name $ map toDeBruijnPat pats

data Pattern
  = PUnit
  | PAny
  | PBind (Maybe String)
  | PCons (Meta String) [Meta Pattern]

instance Eq Pattern where
  PUnit       == PUnit       = True
  PAny        == PAny        = True
  PBind _     == PBind _     = True
  PCons n0 l0 == PCons n1 l1 = n0 == n1 && l0 == l1
  _ == _ = False

instance Show Pattern where
  show PUnit = "()"
  show PAny = "_"
  show (PBind Nothing) = "?"
  show (PBind (Just name)) = name
  show (PCons name []) = unmeta name
  show (PCons name pats) = "(" ++ unmeta name ++ " " ++ intercalate " " (map show pats) ++ ")"

bindingsForPat :: Meta Pattern -> [Maybe String]
bindingsForPat pat =
  case unmeta pat of
    PUnit -> []
    PAny -> []
    PBind b -> [b]
    PCons _ pats -> pats >>= bindingsForPat

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

isCap :: Char -> Bool
isCap ch
  | ch `elem` ['A'..'Z'] || ch == '_' = True
  | otherwise = False
