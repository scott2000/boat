module AST where

import Data.Word
import Data.List
import Data.String

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.Reader
import Control.Monad.State.Strict

type CompileIO = StateT CompileState IO

data CompileState = CompileState
  { anonTypes :: Word64
  , compileErrors :: Set CompileError
  , compileFailed :: Bool }

defaultCompileState :: CompileState
defaultCompileState = CompileState
  { anonTypes = 0
  , compileErrors = Set.empty
  , compileFailed = False }

data CompileError = CompileError
  { errorFile :: Maybe FilePath
  , errorSpan :: Maybe Span
  , errorKind :: ErrorKind
  , errorMessage :: String }
  deriving (Ord, Eq)

data ErrorKind
  = Error
  | Warning
  | Info
  deriving (Ord, Eq)

addError :: MonadState CompileState m => CompileError -> m ()
addError err =
  modify $ \s -> s
    { compileErrors = Set.insert err $ compileErrors s
    , compileFailed = errorKind err == Error || compileFailed s }

displayErrors :: Set CompileError -> IO ()
displayErrors = error "unimplemented"

data Position = Position
  { posLine :: Int
  , posColumn :: Int }
  deriving (Ord, Eq)

data Span = Span
  { spanStart :: Position
  , spanEnd :: Position }
  deriving (Ord, Eq)

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

metaWithEnds :: Meta a -> Meta b -> c -> Meta c
metaWithEnds
    Meta { metaSpan = Just Span { spanStart } }
    Meta { metaSpan = Just Span { spanEnd } }
    x
  = (meta x) { metaSpan = Just Span { spanStart, spanEnd } }
metaWithEnds _ _ x = meta x

data File = File
  { filePath :: FilePath
  , fileLets :: Map Name LetDecl }

instance Show File where
  show file =
    "{- " ++ filePath file ++ " -}\n"
    ++ intercalate "\n" (map showLet $ Map.toList $ fileLets file)
    where
      showLet (name, LetDecl { letBody }) =
        "let " ++ show name ++ " = " ++ indent (show letBody)

defaultFile :: FilePath -> File
defaultFile path = File
  { filePath = path
  , fileLets = Map.empty }

data LetDecl = LetDecl
  { letNameSpan :: Span
  , letBody :: Meta Expr }

fileAddLet :: MonadState CompileState m => (Span, Name) -> Meta Expr -> File -> m File
fileAddLet (nameSpan, name) body file = do
  let
    oldLets = fileLets file
    newDecl = LetDecl
      { letNameSpan = nameSpan
      , letBody = body }
  when (Map.member name oldLets) $
    addError CompileError
      { errorFile = Just (filePath file)
      , errorSpan = Just nameSpan
      , errorKind = Error
      , errorMessage = "duplicate let binding for name `" ++ show name ++ "`" }
  return file { fileLets = Map.insert name newDecl oldLets }

data Of a = Of

of_ :: (Of a -> b) -> a -> b
of_ f x = f Of

class ExprLike a where
  opKind :: Of a -> String
  opUnit :: a
  opNamed :: Meta Path -> a
  opParen :: Meta a -> a
  opUnary :: Meta Path -> Meta a -> a
  opBinary :: Meta Path -> Meta a -> Meta a -> a
  opApply :: Meta a -> Meta a -> Either String a
  opSeq :: Meta a -> Meta a -> Either String a
  opSeq x _ =
    Left ("line breaks not allowed in " ++ opKind `of_` unmeta x)

data Name
  = Identifier String
  | Operator String
  | Unary String
  deriving (Ord, Eq)

instance IsString Name where
  fromString = Identifier

instance Show Name where
  show = \case
    Identifier ident -> ident
    Operator op -> "(" ++ op ++ ")"
    Unary u -> "(unary " ++ u ++ ")"

data Path = Path
  { unpath :: [Name] }
  deriving (Ord, Eq)

instance Show Path where
  show = intercalate "." . map show . unpath

instance IsString Path where
  fromString = Path . map fromString . split
    where
      split "" = [""]
      split ('.':cs) = "" : split cs
      split (c:cs) = (c : first) : rest
        where
          (first:rest) = split cs

data TBase
  = TNamed Path
  | TPoly String
  | TAnon Word64
  deriving Eq

data Type
  = TApp TBase [Meta Type]
  | TParen (Meta Type)
  | TUnaryOp (Meta Path) (Meta Type)
  | TBinOp (Meta Path) (Meta Type) (Meta Type)
  deriving Eq

pattern Core :: Name -> Path
pattern Core name = Path ["core", name]

pattern Local :: Name -> Path
pattern Local name = Path [name]

pattern TFunc :: Meta Type -> Meta Type -> Type
pattern TFunc a b = TApp (TNamed (Core (Operator "->"))) [a, b]

tApp :: [Meta Type] -> Type -> Type
tApp types (TApp base xs) = TApp base (xs ++ types)

data Value
  = VUnit
  | VFun [MatchCase]

instance Show Value where
  show = \case
    VUnit -> "()"
    VFun cases -> 
      "(fun" ++ showCases True cases ++ ")"

instance Eq Value where
  VUnit == VUnit = True
  VFun c0 == VFun c1 =
    c0 == c1
  _ == _ = False

type MatchCase = ([Meta Pattern], Meta Expr)

data Expr
  = EValue Value
  | EGlobal Path
  | EIndex Int (Maybe String)
  | EParen (Meta Expr)
  | EUnaryOp (Meta Path) (Meta Expr)
  | EBinOp (Meta Path) (Meta Expr) (Meta Expr)
  | EApp (Meta Expr) (Meta Expr)
  | ESeq (Meta Expr) (Meta Expr)
  | ELet (Meta Pattern) (Meta Expr) (Meta Expr)
  | EMatchIn [Meta Expr] [MatchCase]

instance ExprLike Expr where
  opKind _ = "expression"
  opUnit = EValue VUnit
  opNamed = EGlobal . unmeta
  opParen expr =
    case unmeta expr of
      EUnaryOp _ _ -> EParen expr
      EBinOp _ _ _ -> EParen expr
      other -> other
  opUnary = EUnaryOp
  opBinary = EBinOp
  opApply a b = Right $ EApp a b
  opSeq a b = Right $ ESeq a b

instance Eq Expr where
  EValue v0 == EValue v1 =
    v0 == v1
  EGlobal n0 == EGlobal n1 =
    n0 == n1
  EIndex x0 _ == EIndex x1 _ =
    x0 == x1
  -- EParen, EUnaryOp, and EBinOp are omitted as they will be removed by later passes
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
    EGlobal name -> show name
    EIndex 0 Nothing -> "?"
    EIndex n Nothing -> "?" ++ show n
    EIndex _ (Just name) -> name
    EParen expr -> show expr
    EUnaryOp Meta { unmeta = Path [Unary op] } expr ->
      "(" ++ op ++ show expr ++ ")"
    EUnaryOp op expr ->
      "(" ++ show op ++ " " ++ show expr ++ ")"
    EBinOp Meta { unmeta = Path [Operator op] } lhs rhs ->
      "(" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ ")"
    EBinOp op lhs rhs ->
      "(" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ ")"
    EApp a b ->
      "(" ++ show a ++ " " ++ show b ++ ")"
    ESeq a b ->
      "(" ++ indent (show a ++ "\n" ++ show b) ++ ")"
    ELet p v e ->
      "(let " ++ show p ++ " =" ++ indent (show v) ++ "\n" ++ show e ++ ")"
    EMatchIn exprs cases ->
      "(match " ++ intercalate " " (map show exprs) ++ showCases False cases ++ ")"

indent :: String -> String
indent = indentLines . lines
  where
    indentLines [one] = " " ++ one
    indentLines rest = "\n  " ++ intercalate "\n  " rest

showCases :: Bool -> [MatchCase] -> String
showCases True [c] = indent (showCase c)
showCases _ cases = "\n  " ++ intercalate "\n  " (map showCase cases)

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
  EParen expr ->
    EParen $ toDeBruijn expr
  EUnaryOp op expr ->
    EUnaryOp op $ toDeBruijn expr
  EBinOp op lhs rhs ->
    EBinOp op (toDeBruijn lhs) (toDeBruijn rhs)
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
      PParen pat ->
        PParen $ toDeBruijnPat pat
      PUnaryOp op pat ->
        PUnaryOp op $ toDeBruijnPat pat
      PBinOp op lhs rhs ->
        PBinOp op (toDeBruijnPat lhs) (toDeBruijnPat rhs)
      PCons name pats ->
        PCons name $ map toDeBruijnPat pats

data Pattern
  = PUnit
  | PAny
  | PBind (Maybe String)
  | PParen (Meta Pattern)
  | PUnaryOp (Meta Path) (Meta Pattern)
  | PBinOp (Meta Path) (Meta Pattern) (Meta Pattern)
  | PCons (Meta Path) [Meta Pattern]

instance ExprLike Pattern where
  opKind _ = "pattern"
  opUnit = PUnit
  opNamed name = PCons name []
  opParen pat =
    case unmeta pat of
      PUnaryOp _ _ -> PParen pat
      PBinOp _ _ _ -> PParen pat
      other -> other
  opUnary = PUnaryOp
  opBinary = PBinOp
  opApply Meta { unmeta = PParen p } x = opApply p x
  opApply Meta { unmeta = PCons name xs } x = Right $ PCons name (xs ++ [x])
  opApply other _ = Left ("pattern does not support parameters: " ++ show other)

instance Eq Pattern where
  PUnit       == PUnit       = True
  PAny        == PAny        = True
  PBind _     == PBind _     = True
  -- PParen, PUnaryOp, and PBinOp are omitted as they will be removed by later passes
  PCons n0 l0 == PCons n1 l1 = n0 == n1 && l0 == l1
  _ == _ = False

instance Show Pattern where
  show = \case
    PUnit -> "()"
    PAny -> "_"
    PBind Nothing -> "?"
    PBind (Just name) -> name
    PUnaryOp Meta { unmeta = Path [Unary op] } pat ->
      "(" ++ op ++ show pat ++ ")"
    PUnaryOp op pat ->
      "(" ++ show op ++ " " ++ show pat ++ ")"
    PBinOp Meta { unmeta = Path [Operator op] } lhs rhs ->
      "(" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ ")"
    PBinOp op lhs rhs ->
      "(" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ ")"
    PCons name [] -> show name
    PCons name pats ->
      "(" ++ show name ++ " " ++ intercalate " " (map show pats) ++ ")"

bindingsForPat :: Meta Pattern -> [Maybe String]
bindingsForPat pat =
  case unmeta pat of
    PUnit -> []
    PAny -> []
    PBind b -> [b]
    PParen pat -> bindingsForPat pat
    PUnaryOp _ pat -> bindingsForPat pat
    PBinOp _ lhs rhs -> bindingsForPat lhs ++ bindingsForPat rhs
    PCons _ pats -> pats >>= bindingsForPat

isLocalIdentifier :: String -> Bool
isLocalIdentifier = not . isCap . head

extractLocalName :: Path -> Maybe String
extractLocalName (Path [Identifier name])
  | isLocalIdentifier name = Just name
extractLocalName _ = Nothing

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

isCap :: Char -> Bool
isCap ch
  | ch `elem` ['A'..'Z'] || ch == '_' = True
  | otherwise = False
