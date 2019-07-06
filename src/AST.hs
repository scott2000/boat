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

type MatchCase = ([Meta Pattern], Meta Expr)

data Expr
  = EIndex Int (Maybe String)
  | EGlobal String
  | EApp (Meta Expr) (Meta Expr)
  | EFun [MatchCase]
  | ELetIn (Meta Pattern) (Meta Expr) (Meta Expr)
  | EMatchIn [Meta Expr] [MatchCase]

instance Eq Expr where
  EIndex x0 _ == EIndex x1 _ =
    x0 == x1
  EGlobal n0 == EGlobal n1 =
    n0 == n1
  EApp a0 b0 == EApp a1 b1 =
    a0 == a1 && b0 == b1
  EFun c0 == EFun c1 =
    c0 == c1
  ELetIn p0 v0 e0 == ELetIn p1 v1 e1 =
    p0 == p1 && v0 == v1 && e0 == e1
  EMatchIn e0 c0 == EMatchIn e1 c1 =
    e0 == e1 && c0 == c1
  _ == _ = False

instance Show Expr where
  show expr =
    case expr of
      EIndex 0 Nothing -> "?"
      EIndex n Nothing -> "?" ++ show n
      EIndex _ (Just name) -> name
      EGlobal name -> name
      EApp a b ->
        "(" ++ show a ++ " " ++ show b ++ ")"
      EFun cases ->
        "(fun" ++ showCases cases ++ ")"
      ELetIn p v e ->
        "(let " ++ show p ++ " =" ++ indent (show v) ++ "\n" ++ show e ++ ")"
      EMatchIn exprs cases ->
        "(match " ++ intercalate " " (map show exprs) ++ " in" ++ showCases cases ++ ")"
    where
      showCases [c] = indent (showCase c)
      showCases cases = "\n  " ++ intercalate "\n  " (map showCase cases)
      showCase (pats, expr) = intercalate " " (map show pats) ++ " ->" ++ indent (show expr)
      indent = indentLines . lines
      indentLines [one] = " " ++ one
      indentLines rest = "\n  " ++ intercalate "\n  " rest

toDeBruijn :: Meta Expr -> Meta Expr
toDeBruijn = fmap $ \case
  EIndex index _ ->
    EIndex index Nothing
  EGlobal name ->
    EGlobal name
  EApp a b ->
    EApp (toDeBruijn a) (toDeBruijn b)
  EFun cases ->
    EFun $ map toDeBruijnCase cases
  ELetIn p v e ->
    ELetIn (toDeBruijnPat p) (toDeBruijn v) (toDeBruijn e)
  EMatchIn exprs cases ->
    EMatchIn (map toDeBruijn exprs) $ map toDeBruijnCase cases
  where
    toDeBruijnCase (pats, expr) = (map toDeBruijnPat pats, toDeBruijn expr)
    toDeBruijnPat = fmap $ \case
      PAny -> PAny
      PBind _ -> PBind Nothing
      PCons name pats ->
        PCons name $ map toDeBruijnPat pats

data Pattern
  = PAny
  | PBind (Maybe String)
  | PCons (Meta String) [Meta Pattern]

instance Eq Pattern where
  PAny        == PAny        = True
  PBind _     == PBind _     = True
  PCons n0 l0 == PCons n1 l1 = n0 == n1 && l0 == l1
  _ == _ = False

instance Show Pattern where
  show PAny = "_"
  show (PBind Nothing) = "?"
  show (PBind (Just name)) = name
  show (PCons name []) = unmeta name
  show (PCons name pats) = "(" ++ unmeta name ++ " " ++ intercalate " " (map show pats) ++ ")"

bindingsForPat :: Meta Pattern -> [Maybe String]
bindingsForPat pat =
  case unmeta pat of
    PAny -> []
    PBind b -> [b]
    PCons _ pats -> pats >>= bindingsForPat

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

isCap :: Char -> Bool
isCap ch
  | ch `elem` ['A'..'Z'] || ch == '_' = True
  | otherwise = False
