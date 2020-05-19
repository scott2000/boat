-- | Defines everything related to the AST used to store parsed code
module Utility.AST
  ( -- * Metadata
    Meta (..)
  , meta
  , metaWithSpan
  , copySpan
  , metaWithEnds
  , pattern DefaultMeta

    -- * Basic Expressions
  , ExprKind (..)
  , MatchCase
  , Expr (..)
  , Value (..)
  , Pattern (..)
  , bindingsForPat
  , Type (..)
  , EffectSet (..)
  , Effect (..)
  , pattern EffectPure
  , Constraint (..)
  , UseModule (..)
  , UseContents (..)

  -- * Functions and Type Applications
  , ReducedApp (..)
  , reduceApply
  , reduceApplyNoInfix
  , findBase
  , pattern TAnyFuncArrow
  , pattern TEffFuncArrow
  , pattern TFuncArrow
  , expandFunction
  , pattern TAnyFunc
  , pattern TEffFunc
  , pattern TFunc

    -- * Parsing and Modifying Expressions
  , Of (..)
  , ExprLike (..)
  , After (..)
  , afterPath
  , AfterMap (..)
  , aDefault

  -- * Global and Local Identifiers
  , isLocalIdentifier
  , extractLocalName
  , extractLocalPath

  -- * Formatting Helper Functions
  , indent
  , effectSuffix
  , effectSuffixStr
  ) where

import Utility.Basics

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.Identity

-- | Stores a value with some additional metadata
data Meta a = Meta
  { -- | The inner value being stored
    unmeta :: a
    -- | The location of the value in its source file
  , metaSpan :: !(Maybe Span)
    -- | The type of a value (if inferred and applicable)
  , metaTy :: !(Maybe Type) }
  deriving (Functor, Foldable, Traversable)

instance Ord a => Ord (Meta a) where
  a `compare` b = unmeta a `compare` unmeta b

instance Eq a => Eq (Meta a) where
  m0 == m1 = unmeta m0 == unmeta m1 && metaTy m0 == metaTy m1

instance Show a => Show (Meta a) where
  showsPrec i = showsPrec i . unmeta

-- | Stores a value with no additional metadata
meta :: a -> Meta a
meta x = Meta
  { unmeta = x
  , metaSpan = Nothing
  , metaTy = Nothing }

-- | Stores a value with a 'Span' taken from another
copySpan :: Meta a -> b -> Meta b
copySpan Meta { metaSpan } x =
  (meta x) { metaSpan }

-- | Stores a value with a certain 'Span'
metaWithSpan :: Span -> a -> Meta a
metaWithSpan span x = (meta x)
  { metaSpan = Just span }

-- | Stores a value with a 'Span' between the two given ends
metaWithEnds :: Meta a -> Meta b -> c -> Meta c
metaWithEnds
    Meta { metaSpan = Just span0 }
    Meta { metaSpan = Just span1 }
    x
  = (meta x) { metaSpan = Just (span0 <> span1) }
metaWithEnds _ _ x = meta x

-- | Represents the different kinds of AST expression
data ExprKind
  -- | A value expression ('Expr')
  = KValue
  -- | A pattern ('Pattern')
  | KPattern
  -- | A type ('Type')
  | KType
  -- | An effect ('Effect')
  | KEffect
  deriving (Ord, Eq)

instance Show ExprKind where
  show = \case
    KValue   -> "value"
    KPattern -> "pattern"
    KType    -> "type"
    KEffect  -> "effect"

-- | A transformation to be applied to an AST
data AfterMap m = AfterMap
  { aExpr :: Meta Expr -> m (Meta Expr)
    -- | A special case used for transforming a use expression
  , aUseExpr :: AfterMap m -> Meta UseModule -> Meta Expr -> m Expr
  , aPattern :: Meta Pattern -> m (Meta Pattern)
  , aType :: Meta Type -> m (Meta Type)
  , aEffect :: Meta Effect -> m (Meta Effect)
    -- | Transformations for 'Path' require an 'ExprKind' to indicate where they are being used
  , aPath :: ExprKind -> Meta Path -> m Path }

-- | A default transformation which does nothing
aDefault :: Monad m => AfterMap m
aDefault = AfterMap
  { aExpr = pure
  , aUseExpr = \m use expr -> EUse use <$> after m expr
  , aPattern = pure
  , aType = pure
  , aEffect = pure
  , aPath = const (pure . unmeta) }

-- | A class for anything that can be transformed with an 'AfterMap'
class After a where
  -- | Applies the transformation represented by the 'AfterMap'
  after :: Monad m => AfterMap m -> Meta a -> m (Meta a)

-- | Wrapper for 'aPath' that more closely matches the signature of 'after'
afterPath :: Monad m => AfterMap m -> ExprKind -> Meta Path -> m (Meta Path)
afterPath m k path = do
  p <- aPath m k path
  return path { unmeta = p }

-- | A wrapper around a set of 'Effect's
newtype EffectSet = EffectSet
  { setEffects :: Set (Meta Effect) }
  deriving (Ord, Eq)

instance After EffectSet where
  after m =
    mapM $ \EffectSet { setEffects } ->
      EffectSet <$> Set.fromList <$> mapM (after m) (Set.toList setEffects)

instance Show EffectSet where
  show EffectSet { setEffects }
    | Set.null setEffects = "Pure"
    | otherwise = intercalate " + " $ map show $ Set.toList setEffects

-- | An effect that can occur in impure code
data Effect
  = EffectNamed Path      -- ^ A named effect
  | EffectPoly String     -- ^ A lowercase effect variable
  | EffectAnon AnonCount  -- ^ An effect left blank to be inferred
  deriving (Ord, Eq)

instance After Effect where
  after m x = do
    x' <- aEffect m x
    forM x' $ \case
      EffectNamed path ->
        EffectNamed <$> aPath m KEffect (path <$ x')
      other ->
        return other

instance Show Effect where
  show = \case
    EffectNamed path -> show path
    EffectPoly name  -> name
    EffectAnon _     -> "_"

-- | Formats a string of |...| bracketed effects to add after a declaration
effectSuffix :: [Meta EffectSet] -> String
effectSuffix = effectSuffixStr . map show

-- | Same as 'effectSuffix', but accepts strings instead
effectSuffixStr :: [String] -> String
effectSuffixStr = concatMap $ \effect ->
  " |" ++ effect ++ "|"

-- | A constraint from a with-clause in a declaration
data Constraint
  = Effect `IsSubEffectOf` EffectSet
  deriving (Ord, Eq)

instance Show Constraint where
  show (effect `IsSubEffectOf` set) =
    show effect ++ " : " ++ show set

-- | A path specifying a single item or module to use
data UseModule
  -- | Use everything in this scope
  = UseAny
  -- | Use a named item and certain sub-items
  | UseModule (Meta Name) UseContents
  deriving (Ord, Eq)

instance Show UseModule where
  show = \case
    UseAny -> "_"
    UseModule name contents ->
      show name ++ show contents

-- | Specifies which sub-items to use in a 'UseModule'
data UseContents
  -- | Use a single sub-module separated by a dot
  = UseDot (Meta UseModule)
  -- | Use all of a list of items (use @[]@ to end use path)
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

-- | The type of an expression
data Type
  = TUnit                                       -- ^ The @()@ type
  | TNamed [Meta EffectSet] (Meta Path)         -- ^ A named type and any effect arguments
  | TPoly String                                -- ^ A lowercase type variable
  | TAnon AnonCount                             -- ^ A type left blank to be inferred
  | TApp (Meta Type) (Meta Type)                -- ^ An application of a type argument to a type
  | TParen (Meta Type)
  | TUnaryOp (Meta Path) (Meta Type)
  | TBinOp (Meta Path) (Meta Type) (Meta Type)
  deriving Eq

instance After Type where
  after m x = do
    x' <- aType m x
    forM x' $ \case
      TNamed effs path ->
        TNamed <$> mapM (after m) effs <*> afterPath m KType path
      TApp a b ->
        TApp <$> after m a <*> after m b
      TParen a ->
        TParen <$> after m a
      TUnaryOp path a ->
        TUnaryOp <$> afterPath m KType path <*> after m a
      TBinOp path a b ->
        TBinOp <$> afterPath m KType path <*> after m a <*> after m b
      other ->
        return other

instance Show Type where
  show = \case
    TUnit -> "()"
    TNamed effs path -> show path ++ effectSuffix effs
    TPoly name -> name
    TAnon _ -> "_"
    TEffFunc effs a b ->
      "(" ++ show a ++ " -|" ++ show effs ++ "|> " ++ show b ++ ")"
    TFunc a b ->
      "(" ++ show a ++ " -> " ++ show b ++ ")"
    TApp a b ->
      "(" ++ show a ++ " " ++ show b ++ ")"
    TParen ty -> "{" ++ show ty ++ "}"
    TUnaryOp Meta { unmeta = Path [Unary op] } ty ->
      "{" ++ op ++ show ty ++ "}"
    TUnaryOp op ty ->
      "{" ++ show op ++ " " ++ show ty ++ "}"
    TBinOp Meta { unmeta = Path [Operator op] } lhs rhs ->
      "{" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ "}"
    TBinOp op lhs rhs ->
      "{" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ "}"

-- | A form of a 'Type' with all applications reduced
data ReducedApp = ReducedApp
  { reducedType :: Meta Type
  , reducedArgs :: [Meta Type] }

-- | Try to reduce all applications, otherwise return the conflicting infix operators
reduceApply :: Meta Type -> Either (Meta Path, Meta Path) ReducedApp
reduceApply typeWithMeta =
  case unmeta typeWithMeta of
    TApp a b -> do
      ReducedApp ty args <- reduceApply a
      Right $ ReducedApp ty (args ++ [b])
    TParen ty ->
      reduceApply ty
    TUnaryOp a Meta { unmeta = TBinOp b _ _ } ->
      Left (a, b)
    TBinOp a _ Meta { unmeta = TBinOp b _ _ } ->
      Left (a, b)
    TUnaryOp path ty ->
      Right $ ReducedApp (copySpan path $ TNamed [] path) [ty]
    TBinOp path a b ->
      Right $ ReducedApp (copySpan path $ TNamed [] path) [a, b]
    _ ->
      Right $ ReducedApp typeWithMeta []

-- | Try to reduce all applications but don't allow infix operators
reduceApplyNoInfix :: Meta Type -> Either (Meta Path) ReducedApp
reduceApplyNoInfix typeWithMeta =
  case unmeta typeWithMeta of
    TApp a b -> do
      ReducedApp ty args <- reduceApplyNoInfix a
      Right $ ReducedApp ty (args ++ [b])
    TParen ty ->
      reduceApplyNoInfix ty
    TUnaryOp path _ ->
      Left path
    TBinOp path _ _ ->
      Left path
    _ ->
      Right $ ReducedApp typeWithMeta []

-- | Find the base of a series of applications and the number of applications removed
findBase :: Meta Type -> (Meta Type, Int)
findBase = go 0
  where
    go n ty =
      case unmeta ty of
        TApp a _ ->
          go (n + 1) a
        _ ->
          (ty, n)

-- | Create a function type from a series of argument types and a return type
expandFunction :: [Meta Type] -> Meta Type -> Meta Type
expandFunction [] ty = ty
expandFunction (ty:types) ret =
  meta $ TFunc ty $ expandFunction types ret

-- | Matches any value and ignores metadata completely
pattern DefaultMeta :: a -> Meta a
pattern DefaultMeta x <- Meta { unmeta = x }
  where DefaultMeta = meta

-- | A function arrow with a list of effect parameters
pattern TAnyFuncArrow :: [Meta EffectSet] -> Type
pattern TAnyFuncArrow effs = TNamed effs (DefaultMeta (Core (Operator "->")))

-- | A function arrow with a single effect parameter
pattern TEffFuncArrow :: Meta EffectSet -> Type
pattern TEffFuncArrow eff = TAnyFuncArrow [eff]

-- | A function arrow with no effect parameters
pattern TFuncArrow :: Type
pattern TFuncArrow = TAnyFuncArrow []

-- | A function type with a list of effect parameters
pattern TAnyFunc :: [Meta EffectSet] -> Meta Type -> Meta Type -> Type
pattern TAnyFunc effs a b =
  TApp (DefaultMeta (TApp (DefaultMeta (TAnyFuncArrow effs)) a)) b

-- | A function type with a single effect parameter
pattern TEffFunc :: Meta EffectSet -> Meta Type -> Meta Type -> Type
pattern TEffFunc eff a b = TAnyFunc [eff] a b

-- | A function type with no effect parameters
pattern TFunc :: Meta Type -> Meta Type -> Type
pattern TFunc a b = TAnyFunc [] a b

-- | An effect representing pure code
pattern EffectPure :: Effect
pattern EffectPure = EffectNamed (Core (Identifier "Pure"))

-- | A concrete value produced by evaluating an expression
data Value
  = VUnit                   -- ^ The @()@ value
  | VFun [MatchCase]        -- ^ A function value with match cases for its inputs
  | VDataCons Path [Value]  -- ^ An evaluated data constructor

instance Show Value where
  show = \case
    VUnit -> "()"
    VFun cases ->
      "(fun" ++ showCases True cases ++ ")"
    VDataCons path [] ->
      show path
    VDataCons path vals ->
      "(" ++ show path ++ " " ++ intercalate " " (map show vals) ++ ")"

instance Eq Value where
  VUnit == VUnit = True
  VFun c0 == VFun c1 =
    c0 == c1
  _ == _ = False

-- | A single case in a function or match expression
type MatchCase = ([Meta Pattern], Meta Expr)

-- | Shows a set of match cases, optionally allowing them to be on one line if short
showCases :: Bool -> [MatchCase] -> String
showCases True [c] = indent (showCase c)
showCases _ cases = "\n  " ++ intercalate "\n  " (map showCase cases)

-- | Shows a single match case
showCase :: MatchCase -> String
showCase (pats, expr) = intercalate " " (map show pats) ++ " ->" ++ indent (show expr)

-- | An expression that can be used to produce a 'Value'
data Expr
  = EValue Value                                -- ^ Lifts a 'Value' to be an expression
  | EGlobal Path                                -- ^ A global binding for a value
  | EIndex Int (Maybe String)                   -- ^ A local value with an index and optional name
  | EApp (Meta Expr) (Meta Expr)                -- ^ An application of an argument to a function
  | ESeq (Meta Expr) (Meta Expr)                -- ^ Evaluates one expression and returns the other
  | ELet (Meta Pattern) (Meta Expr) (Meta Expr) -- ^ Binds an expression to a pattern for its body
  | EMatchIn [Meta Expr] [MatchCase]            -- ^ Matches some expressions against some match cases
  | EUse (Meta UseModule) (Meta Expr)           -- ^ Imports some values into scope for its body
  | ETypeAscribe (Meta Expr) (Meta Type)        -- ^ Ascribes a type to an expression
  | EDataCons Path [Meta Expr]                  -- ^ The same as 'VDataCons' but with expression arguments
  | EParen (Meta Expr)
  | EUnaryOp (Meta Path) (Meta Expr)
  | EBinOp (Meta Path) (Meta Expr) (Meta Expr)

instance After Expr where
  after m x = do
    x' <- aExpr m x
    forM x' $ \case
      EValue (VFun cases) ->
        EValue . VFun <$> afterCases cases
      EGlobal path ->
        EGlobal <$> aPath m KValue (path <$ x')
      EApp a b ->
        EApp <$> after m a <*> after m b
      ESeq a b ->
        ESeq <$> after m a <*> after m b
      ELet pat val expr ->
        ELet <$> after m pat <*> after m val <*> after m expr
      EMatchIn exprs cases ->
        EMatchIn <$> mapM (after m) exprs <*> afterCases cases
      EUse use a ->
        aUseExpr m m use a
      ETypeAscribe a ty ->
        ETypeAscribe <$> after m a <*> after m ty
      EDataCons path exprs -> do
        p <- aPath m KValue (path <$ x')
        s <- mapM (after m) exprs
        return $ EDataCons p s
      EParen a ->
        EParen <$> after m a
      EUnaryOp path a ->
        EUnaryOp <$> afterPath m KValue path <*> after m a
      EBinOp path a b ->
        EBinOp <$> afterPath m KValue path <*> after m a <*> after m b
      other ->
        return other
    where
      afterCases =
        mapM $ \(pats, expr) ->
          (,) <$> forM pats (after m) <*> after m expr

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
  EUse u0 e0 == EUse u1 e1 =
    u0 == u1 && e0 == e1
  ETypeAscribe e0 t0 == ETypeAscribe e1 t1 =
    e0 == e1 && t0 == t1
  EDataCons p0 e0 == EDataCons p1 e1 =
    e0 == e1 && p0 == p1
  -- EParen, EUnaryOp, and EBinOp are omitted as they will be removed by later passes
  _ == _ = False

instance Show Expr where
  show = \case
    EValue val -> show val
    EGlobal name -> show name
    EIndex 0 Nothing -> "?"
    EIndex n Nothing -> "?" ++ show n
    EIndex _ (Just name) -> name
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
    EDataCons path [] ->
      show path
    EDataCons path exprs ->
      "(" ++ show path ++ " " ++ intercalate " " (map show exprs) ++ ")"
    EParen expr -> "{" ++ show expr ++ "}"
    EUnaryOp Meta { unmeta = Path [Unary op] } expr ->
      "{" ++ op ++ show expr ++ "}"
    EUnaryOp op expr ->
      "{" ++ show op ++ " " ++ show expr ++ "}"
    EBinOp Meta { unmeta = Path [Operator op] } lhs rhs ->
      "{" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ "}"
    EBinOp op lhs rhs ->
      "{" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ "}"

-- | A pattern which can match a value and bind variables
data Pattern
  = PUnit                                             -- ^ The @()@ pattern
  | PAny                                              -- ^ Matches anything and ignores it
  | PBind (Maybe String)                              -- ^ Matches anything and creates a binding
  | PCons (Meta Path) [Meta Pattern]                  -- ^ Tries to match a data type constructor
  | PTypeAscribe (Meta Pattern) (Meta Type)           -- ^ Ascribes a type to a pattern
  | PParen (Meta Pattern)
  | PUnaryOp (Meta Path) (Meta Pattern)
  | PBinOp (Meta Path) (Meta Pattern) (Meta Pattern)

instance After Pattern where
  after m x = do
    x' <- aPattern m x
    forM x' $ \case
      PCons path xs ->
        PCons <$> afterPath m KPattern path <*> mapM (after m) xs
      PTypeAscribe a ty ->
        PTypeAscribe <$> after m a <*> after m ty
      PParen a ->
        PParen <$> after m a
      PUnaryOp path a ->
        PUnaryOp <$> afterPath m KPattern path <*> after m a
      PBinOp path a b ->
        PBinOp <$> afterPath m KPattern path <*> after m a <*> after m b
      other ->
        return other

instance Eq Pattern where
  PUnit   == PUnit   = True
  PAny    == PAny    = True
  PBind _ == PBind _ = True
  PCons n0 l0 == PCons n1 l1 =
    n0 == n1 && l0 == l1
  PTypeAscribe p0 t0 == PTypeAscribe p1 t1 =
    p0 == p1 && t0 == t1
  -- PParen, PUnaryOp, and PBinOp are omitted as they will be removed by later passes
  _ == _ = False

instance Show Pattern where
  show = \case
    PUnit -> "()"
    PAny -> "_"
    PBind Nothing -> "?"
    PBind (Just name) -> name
    PCons name [] -> show name
    PCons name pats ->
      "(" ++ show name ++ " " ++ intercalate " " (map show pats) ++ ")"
    PTypeAscribe pat ty ->
      "(" ++ show pat ++ " : " ++ show ty ++ ")"
    PParen pat -> "{" ++ show pat ++ "}"
    PUnaryOp Meta { unmeta = Path [Unary op] } pat ->
      "{" ++ op ++ show pat ++ "}"
    PUnaryOp op pat ->
      "{" ++ show op ++ " " ++ show pat ++ "}"
    PBinOp Meta { unmeta = Path [Operator op] } lhs rhs ->
      "{" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ "}"
    PBinOp op lhs rhs ->
      "{" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ "}"

-- | Makes a list of all local variables created by the pattern
bindingsForPat :: Meta Pattern -> [Maybe String]
bindingsForPat pat =
  case unmeta pat of
    PUnit -> []
    PAny -> []
    PBind b -> [b]
    PCons _ pats -> pats >>= bindingsForPat
    PTypeAscribe pat _ -> bindingsForPat pat
    PParen pat -> bindingsForPat pat
    PUnaryOp _ pat -> bindingsForPat pat
    PBinOp _ lhs rhs -> bindingsForPat lhs ++ bindingsForPat rhs

-- | Indents a block of code if it is multiline
indent :: String -> String
indent = indentLines . lines
  where
    indentLines [one] = " " ++ one
    indentLines rest = "\n  " ++ intercalate "\n  " rest

-- | Checks if a string is a valid local identifier (lowercase first letter)
isLocalIdentifier :: String -> Bool
isLocalIdentifier = not . isCap . head

-- | Tries to get a local identifier from a name
extractLocalName :: Name -> Maybe String
extractLocalName (Identifier name)
  | isLocalIdentifier name = Just name
extractLocalName _ = Nothing

-- | Tries to get a local identifier from a path
extractLocalPath :: Path -> Maybe String
extractLocalPath (Path [name]) = extractLocalName name
extractLocalPath _ = Nothing

-- | A placeholder type to be used in 'opKind' to identify the class instance
data Of a = Of

-- | A class representing something that is similar to an 'Expr' for parsing
class ExprLike a where
  -- | Returns the name of the kind of expression being parsed
  opKind :: Of a -> String
  -- | Returns a representation for @()@
  opUnit :: a
  -- | Creates a named expression from a path
  opNamed :: Meta Path -> a
  -- | Creates an expression in parentheses
  opParen :: Meta a -> a
  -- | Creates an expression with a unary operator
  opUnary :: Meta Path -> Meta a -> a
  -- | Creates an expression with a binary operator
  opBinary :: Meta Path -> Meta a -> Meta a -> a
  -- | Tries to create an application of two expressions
  opApply :: Meta a -> Meta a -> Either (Meta String) a

  -- | If sequencing is supported, create a sequence of two expressions
  opSeq :: Maybe (Meta a -> Meta a -> a)
  opSeq = Nothing

  -- | If effect application is supported, try to create an effect application
  opEffectApply :: Maybe (Meta a -> Meta EffectSet -> Either (Meta String) a)
  opEffectApply = Nothing

instance ExprLike Type where
  opKind _ = "type"
  opUnit = TUnit
  opNamed = TNamed []
  opParen ty =
    case unmeta ty of
      TUnaryOp _ _ -> TParen ty
      TBinOp _ _ _ -> TParen ty
      other -> other
  opUnary = TUnaryOp
  opBinary = TBinOp
  opApply a b = Right $ TApp a b
  opEffectApply = Just effectApply
    where
      effectApply Meta { unmeta = TNamed es path } e =
        Right $ TNamed (es ++ [e]) path
      effectApply _ e =
        Left $ copySpan e "effect arguments can only occur immediately following a named type"

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
  opApply Meta { unmeta = PCons name xs } x =
    Right $ PCons name (xs ++ [x])
  opApply _ x =
    Left $ copySpan x "pattern arguments can only occur immediately following a named pattern"

