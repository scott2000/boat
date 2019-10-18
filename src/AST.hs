module AST where

import Basics

import Data.Word
import Data.List
import Data.Bifunctor

import Control.Monad.Identity

data Meta a = Meta
  { unmeta :: a
  , metaTy :: !(Maybe Type)
  , metaSpan :: !(Maybe Span) }
  deriving (Functor, Foldable, Traversable)

instance Ord a => Ord (Meta a) where
  a `compare` b = unmeta a `compare` unmeta b

instance Eq a => Eq (Meta a) where
  m0 == m1 = unmeta m0 == unmeta m1 && metaTy m0 == metaTy m1

instance Show a => Show (Meta a) where
  showsPrec i = showsPrec i . unmeta

meta :: a -> Meta a
meta x = Meta
  { unmeta = x
  , metaTy = Nothing
  , metaSpan = Nothing }

copySpan :: Meta a -> b -> Meta b
copySpan Meta { metaSpan } x =
  (meta x) { metaSpan }

metaWithSpan :: Span -> a -> Meta a
metaWithSpan span x = (meta x)
  { metaSpan = Just span }

metaWithEnds :: Meta a -> Meta b -> c -> Meta c
metaWithEnds
    Meta { metaSpan = Just span0 }
    Meta { metaSpan = Just span1 }
    x
  = (meta x) { metaSpan = Just (span0 <> span1) }
metaWithEnds _ _ x = meta x

data UseModule
  = UseAny
  | UseModule (Meta Name) UseContents
  deriving (Ord, Eq)

instance Show UseModule where
  show = \case
    UseAny -> "_"
    UseModule name contents ->
      show name ++ show contents

data UseContents
  = UseDot (Meta UseModule)
  | UseAll [Meta UseModule]
  deriving (Ord, Eq)

instance Show UseContents where
  show = \case
    UseDot rest ->
      '.' : show rest
    UseAll [] ->
      ""
    UseAll rest ->
      " (" ++ intercalate ", " (map show rest) ++ ")"

-- TODO: visitPath, visitType, visitAll?

data Type
  = TNamed Path
  | TPoly String
  | TAnon Word64
  | TParen (Meta Type)
  | TUnaryOp (Meta Path) (Meta Type)
  | TBinOp (Meta Path) (Meta Type) (Meta Type)
  | TApp (Meta Type) (Meta Type)
  deriving Eq

afterType :: Monad m
          => (Meta Type -> m (Meta Type))
          -> (Meta Path -> m Path)
          -> Meta Type
          -> m (Meta Type)
afterType t h = go
  where
    h' path = (<$ path) <$> h path
    go x = do
      x' <- t x
      forM x' $ \case
        TNamed path ->
          TNamed <$> h (path <$ x')
        TParen a ->
          TParen <$> go a
        TUnaryOp path a ->
          TUnaryOp <$> h' path <*> go a
        TBinOp path a b ->
          TBinOp <$> h' path <*> go a <*> go b
        TApp a b ->
          TApp <$> go a <*> go b
        other ->
          return other

instance Show Type where
  show = \case
    TNamed path -> show path
    TPoly name -> name
    TAnon _ -> "_"
    TParen ty -> show ty
    TUnaryOp Meta { unmeta = Path [Unary op] } ty ->
      "{" ++ op ++ show ty ++ "}"
    TUnaryOp op ty ->
      "{" ++ show op ++ " " ++ show ty ++ "}"
    TBinOp Meta { unmeta = Path [Operator op] } lhs rhs ->
      "{" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ "}"
    TBinOp op lhs rhs ->
      "{" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ "}"
    TApp a b ->
      "(" ++ show a ++ " " ++ show b ++ ")"

reduceApply :: Meta Type -> Either String (Meta Type, [Meta Type])
reduceApply typeWithMeta =
  case unmeta typeWithMeta of
    TParen ty ->
      reduceApply ty
    TUnaryOp path Meta { unmeta = TBinOp _ _ _ } ->
      opError path
    TBinOp path _ Meta { unmeta = TBinOp _ _ _ } ->
      opError path
    TUnaryOp path ty ->
      Right (TNamed <$> path, [ty])
    TBinOp path a b ->
      Right (TNamed <$> path, [a, b])
    TApp a b -> do
      second (++ [b]) <$> reduceApply a
    other ->
      Right (typeWithMeta, [])
  where
    opError path =
      Left ("cannot resolve relative operator precedence of `" ++ show path ++ "` without explicit parentheses")

expandFunction :: [Meta Type] -> Meta Type -> Meta Type
expandFunction [] ty = ty
expandFunction (ty:types) ret =
  meta $ TFunc ty $ expandFunction types ret

pattern DefaultMeta :: a -> Meta a
pattern DefaultMeta x <- Meta { unmeta = x }
  where DefaultMeta = meta

pattern TFuncArrow :: Type
pattern TFuncArrow = TNamed (Core (Operator "->"))

pattern TFunc :: Meta Type -> Meta Type -> Type
pattern TFunc a b =
  -- using TFuncArrow here triggers a GHC bug with pattern synonyms
  TApp (DefaultMeta (TApp (DefaultMeta (TNamed (Core (Operator "->")))) a)) b

data Value
  = VUnit
  | VFun [MatchCase]
  | VDataCons Path Name [Value]

instance Show Value where
  show = \case
    VUnit -> "()"
    VFun cases ->
      "(fun" ++ showCases True cases ++ ")"
    VDataCons _ name [] ->
      show name
    VDataCons _ name vals ->
      "(" ++ show name ++ " " ++ intercalate " " (map show vals) ++ ")"

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
  | EUse (Meta UseModule) (Meta Expr)
  | ETypeAscribe (Meta Expr) (Meta Type)
  | EDataCons Path Name [Meta Expr]

afterExpr :: Monad m
          => (Meta Expr -> m (Meta Expr))
          -> (Meta Pattern -> m (Meta Pattern))
          -> (Meta Type -> m (Meta Type))
          -> (Meta Path -> m Path)
          -> Meta Expr
          -> m (Meta Expr)
afterExpr e p t h = go
  where
    h' path = (<$ path) <$> h path
    go x = do
      x' <- e x
      forM x' $ \case
        EValue (VFun cases) ->
          EValue . VFun <$> afterCases cases
        EGlobal path ->
          EGlobal <$> h (path <$ x')
        EParen a ->
          EParen <$> go a
        EUnaryOp path a ->
          EUnaryOp <$> h' path <*> go a
        EBinOp path a b ->
          EBinOp <$> h' path <*> go a <*> go b
        EApp a b ->
          EApp <$> go a <*> go b
        ESeq a b ->
          ESeq <$> go a <*> go b
        ELet pat val expr ->
          ELet <$> afterPattern p t h pat <*> go val <*> go expr
        EMatchIn exprs cases ->
          EMatchIn <$> mapM go exprs <*> afterCases cases
        EUse m a ->
          EUse m <$> go a
        ETypeAscribe a ty ->
          ETypeAscribe <$> go a <*> afterType t h ty
        EDataCons path name exprs ->
          (\p s -> EDataCons p name s)
          <$> h (path <$ x') <*> mapM go exprs
        other ->
          return other
    afterCases =
      mapM $ \(pats, expr) ->
        (,) <$> forM pats (afterPattern p t h) <*> go expr

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
  EUse u0 e0 == EUse u1 e1 =
    u0 == u1 && e0 == e1
  ETypeAscribe e0 t0 == ETypeAscribe e1 t1 =
    e0 == e1 && t0 == t1
  EDataCons p0 n0 e0 == EDataCons p1 n1 e1 =
    e0 == e1 && n0 == n1 && p0 == p1
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
      "{" ++ op ++ show expr ++ "}"
    EUnaryOp op expr ->
      "{" ++ show op ++ " " ++ show expr ++ "}"
    EBinOp Meta { unmeta = Path [Operator op] } lhs rhs ->
      "{" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ "}"
    EBinOp op lhs rhs ->
      "{" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ "}"
    EApp a b ->
      "(" ++ show a ++ " " ++ show b ++ ")"
    ESeq a b ->
      "(" ++ indent (show a ++ "\n" ++ show b) ++ ")"
    ELet p v e ->
      "(let " ++ show p ++ " =" ++ indent (show v) ++ "\n" ++ show e ++ ")"
    EMatchIn exprs cases ->
      "(match " ++ intercalate " " (map show exprs) ++ showCases False cases ++ ")"
    EUse u e ->
      "(use " ++ show u ++ "\n" ++ show e ++ ")"
    ETypeAscribe expr ty ->
      "(" ++ show expr ++ " : " ++ show ty ++ ")"
    EDataCons _ name [] ->
      show name
    EDataCons _ name exprs ->
      "(" ++ show name ++ " " ++ intercalate " " (map show exprs) ++ ")"

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
  EUse u e ->
    EUse u $ toDeBruijn e
  ETypeAscribe expr ty ->
    ETypeAscribe (toDeBruijn expr) ty
  EDataCons path name exprs ->
    EDataCons path name $ map toDeBruijn exprs
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
      PTypeAscribe pat ty ->
        PTypeAscribe (toDeBruijnPat pat) ty

data Pattern
  = PUnit
  | PAny
  | PBind (Maybe String)
  | PParen (Meta Pattern)
  | PUnaryOp (Meta Path) (Meta Pattern)
  | PBinOp (Meta Path) (Meta Pattern) (Meta Pattern)
  | PCons (Meta Path) [Meta Pattern]
  | PTypeAscribe (Meta Pattern) (Meta Type)

afterPattern :: forall m. Monad m
             => (Meta Pattern -> m (Meta Pattern))
             -> (Meta Type -> m (Meta Type))
             -> (Meta Path -> m Path)
             -> Meta Pattern
             -> m (Meta Pattern)
afterPattern p t h = go
  where
    h' path = (<$ path) <$> h path
    go x = do
      x' <- p x
      forM x' $ \case
        PParen a ->
          PParen <$> go a
        PUnaryOp path a ->
          PUnaryOp <$> h' path <*> go a
        PBinOp path a b ->
          PBinOp <$> h' path <*> go a <*> go b
        PCons path xs ->
          PCons <$> h' path <*> mapM go xs
        PTypeAscribe a ty ->
          PTypeAscribe <$> go a <*> afterType t h ty
        other ->
          return other

instance Eq Pattern where
  PUnit   == PUnit   = True
  PAny    == PAny    = True
  PBind _ == PBind _ = True
  -- PParen, PUnaryOp, and PBinOp are omitted as they will be removed by later passes
  PCons n0 l0 == PCons n1 l1 =
    n0 == n1 && l0 == l1
  PTypeAscribe p0 t0 == PTypeAscribe p1 t1 =
    p0 == p1 && t0 == t1
  _ == _ = False

instance Show Pattern where
  show = \case
    PUnit -> "()"
    PAny -> "_"
    PBind Nothing -> "?"
    PBind (Just name) -> name
    PUnaryOp Meta { unmeta = Path [Unary op] } pat ->
      "{" ++ op ++ show pat ++ "}"
    PUnaryOp op pat ->
      "{" ++ show op ++ " " ++ show pat ++ "}"
    PBinOp Meta { unmeta = Path [Operator op] } lhs rhs ->
      "{" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ "}"
    PBinOp op lhs rhs ->
      "{" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ "}"
    PCons name [] -> show name
    PCons name pats ->
      "(" ++ show name ++ " " ++ intercalate " " (map show pats) ++ ")"
    PTypeAscribe pat ty ->
      "(" ++ show pat ++ " : " ++ show ty ++ ")"

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
    PTypeAscribe pat _ -> bindingsForPat pat

isLocalIdentifier :: String -> Bool
isLocalIdentifier = not . isCap . head

extractLocalName :: Name -> Maybe String
extractLocalName (Identifier name)
  | isLocalIdentifier name = Just name
extractLocalName _ = Nothing

extractLocalPath :: Path -> Maybe String
extractLocalPath (Path [name]) = extractLocalName name
extractLocalPath _ = Nothing

idPath :: Monad m => Meta Path -> m Path
idPath = return . unmeta

type Associator m = forall t. ContainsOp t => [UnOpOrExpr t] -> m (Meta t)

data UnOpOrExpr a
  = UnOp (Meta Path)
  | UnExpr (Meta a)

instance Show a => Show (UnOpOrExpr a) where
  show = \case
    UnOp path -> "`" ++ show path ++ "`"
    UnExpr expr -> show expr

class Show a => ContainsOp a where
  toUnOpList :: Meta a -> [UnOpOrExpr a]
  applyUnary :: Meta Path -> Meta a -> Meta a
  applyBinary :: Meta Path -> Meta a -> Meta a -> Meta a
  reassociate :: Monad m => Associator m -> Meta a -> m (Meta a)

instance ContainsOp Type where
  toUnOpList x =
    -- strip leading parentheses
    case unmeta x of
      TParen a ->
        toUnOpList a
      _ ->
        go x
    where
      go x =
        case unmeta x of
          TParen a ->
            [UnExpr a]
          TUnaryOp path a ->
            UnOp path : toUnOpList a
          TBinOp path a b ->
            UnExpr a : UnOp path : toUnOpList b
          _ ->
            [UnExpr x]

  applyUnary path a =
    metaWithEnds path a $ TApp (TNamed <$> path) a

  applyBinary path a b =
    metaWithEnds a b $
      TApp (metaWithEnds a path $ TApp (TNamed <$> path) a) b

  reassociate f =
    afterType (f . toUnOpList) idPath

instance ContainsOp Expr where
  toUnOpList x =
    -- strip leading parentheses
    case unmeta x of
      EParen a ->
        toUnOpList a
      _ ->
        go x
    where
      go x =
        case unmeta x of
          EParen a ->
            [UnExpr a]
          EUnaryOp path a ->
            UnOp path : toUnOpList a
          EBinOp path a b ->
            UnExpr a : UnOp path : toUnOpList b
          _ ->
            [UnExpr x]

  applyUnary path a =
    metaWithEnds path a $ EApp (EGlobal <$> path) a

  applyBinary path a b =
    metaWithEnds a b $
      EApp (metaWithEnds a path $ EApp (EGlobal <$> path) a) b

  reassociate f =
    afterExpr
      (f . toUnOpList)
      (f . toUnOpList)
      (f . toUnOpList)
      idPath

instance ContainsOp Pattern where
  toUnOpList x =
    -- strip leading parentheses
    case unmeta x of
      PParen a ->
        toUnOpList a
      _ ->
        go x
    where
      go x =
        case unmeta x of
          PParen a ->
            [UnExpr a]
          PUnaryOp path a ->
            UnOp path : toUnOpList a
          PBinOp path a b ->
            UnExpr a : UnOp path : toUnOpList b
          _ ->
            [UnExpr x]

  applyUnary path a =
    metaWithEnds path a $ PCons path [a]

  applyBinary path a b =
    metaWithEnds a b $ PCons path [a, b]

  reassociate f =
    afterPattern
      (f . toUnOpList)
      (f . toUnOpList)
      idPath

data Of a = Of

class ExprLike a where
  opKind :: Of a -> String
  opUnit :: a
  opNamed :: Meta Path -> a
  opParen :: Meta a -> a
  opUnary :: Meta Path -> Meta a -> a
  opBinary :: Meta Path -> Meta a -> Meta a -> a
  opApply :: Meta a -> Meta a -> Either String a
  opSeq :: Maybe (Meta a -> Meta a -> a)
  opSeq = Nothing

instance ExprLike Type where
  opKind _ = "type"
  opUnit = TNamed $ Core $ Identifier "Unit"
  opNamed = TNamed . unmeta
  opParen = TParen
  opUnary = TUnaryOp
  opBinary = TBinOp
  opApply a b = Right $ TApp a b

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
  opSeq = Just ESeq

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

