-- | Defines everything related to the AST used to store parsed code
module Utility.AST
  ( -- * Metadata
    Meta (..)
  , MetaR
  , withInfo
  , copyInfo
  , DefaultInfo (..)
  , pattern DefaultInfo
  , pattern DefaultMeta
  , meta
  , SpanInfo (..)
  , getSpan
  , withEnds
  , FileInfo (..)
  , InFile (..)
  , getFile
  , withFile
  , TypeInfo (..)
  , Typed (..)
  , getType
  , withType

    -- * Basic Expressions
  , ExprKind (..)
  , MatchCase
  , Expr (..)
  , Value (..)
  , Pattern (..)
  , bindingsForPat
  , assertUniqueBindings
  , Type (..)
  , EffectSet (..)
  , emptyEffectSet
  , singletonEffectSet
  , Effect (..)
  , pattern EffectPure
  , pattern EffectVoid
  , UseModule (..)
  , UseContents (..)

    -- * Functions and Type Applications
  , ReducedApp (..)
  , reduceApply
  , reduceApplyNoInfix
  , findBase
  , expandFunction
  , pattern TAnyFuncArrow
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
import Data.Maybe

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

-- | Stores some information as metadata along with a value
data Meta info a = (:&:)
  { -- | The plain value without the metadata
    unmeta :: a
    -- | The information being stored with the value
  , getInfo :: !info }
  deriving (Functor, Foldable, Traversable)

-- | Like 'Meta', but the second argument is also passed the information
type MetaR info expr = Meta info (expr info)

infixr 1 :&:

instance Ord a => Ord (Meta info a) where
  (x :&: _) `compare` (y :&: _) =
    x `compare` y

instance Eq a => Eq (Meta info a) where
  (x :&: _) == (y :&: _) =
    x == y

instance Show a => Show (Meta info a) where
  showsPrec i = showsPrec i . unmeta

-- | Attaches some information to a value
withInfo :: info -> a -> Meta info a
withInfo = flip (:&:)

-- | Copies the information from something to another
copyInfo :: Meta info a -> b -> Meta info b
copyInfo (_ :&: info) x = x :&: info

-- | Metadata that has a reasonable default value
class DefaultInfo info where
  -- | The default value
  defaultInfo :: info

instance DefaultInfo () where
  defaultInfo = ()

instance DefaultInfo Span where
  defaultInfo = NoSpan

-- | Matches any information and uses 'defaultInfo' if used as an expression
pattern DefaultInfo :: DefaultInfo info => info
pattern DefaultInfo <- _
  where DefaultInfo = defaultInfo

-- | Bidirectional pattern for when the specific metadata is not important and has a reasonable default
pattern DefaultMeta :: DefaultInfo info => a -> Meta info a
pattern DefaultMeta x = x :&: DefaultInfo

-- | A short form of 'DefaultMeta' that can only be used as an expression
meta :: DefaultInfo info => a -> Meta info a
meta = DefaultMeta

-- | Metadata that contains span information
class SpanInfo info where
  -- | Extracts the span information
  infoSpan :: info -> Span

instance SpanInfo Span where
  infoSpan = id

-- | Gets the span information of a value
getSpan :: SpanInfo info => Meta info a -> Span
getSpan = infoSpan . getInfo

-- | Produces a value with a span that has the first two values as its ends
withEnds :: Meta Span a -> Meta Span b -> c -> Meta Span c
withEnds (_ :&: start) (_ :&: end) =
  withInfo $ start <> end

-- | Metadata that contains file information
class FileInfo info where
  -- | Extracts the file information
  infoFile :: info -> FilePath

-- | Adds file information to a value (usually a 'Span')
data InFile info = (:/:)
  { -- | The file path where the item can be found
    getFile' :: !FilePath
    -- | The rest of the information
  , unfile :: !info }

instance SpanInfo info => SpanInfo (InFile info) where
  infoSpan = infoSpan . unfile

instance DefaultInfo info => DefaultInfo (InFile info) where
  defaultInfo = NoFile :/: defaultInfo

instance FileInfo (InFile info) where
  infoFile = getFile'

instance TypeInfo info => TypeInfo (InFile info) where
  infoType = infoType . unfile

-- | Gets the file information of a value
getFile :: FileInfo info => Meta info a -> FilePath
getFile = infoFile . getInfo

-- | Adds file information to a value
withFile :: FilePath -> Meta info a -> Meta (InFile info) a
withFile file (x :&: info) = (x :&: file :/: info)

-- | Metadata that contains type information
class TypeInfo info where
  -- | Extracts the type information
  infoType :: info -> Type ()

-- | Adds type information to a value
data Typed info = (:::)
  { -- | The rest of the information
    untype :: !info
    -- | The type of the item
  , getType' :: !(Type ()) }

instance SpanInfo info => SpanInfo (Typed info) where
  infoSpan = infoSpan . untype

instance FileInfo info => FileInfo (Typed info) where
  infoFile = infoFile . untype

instance TypeInfo (Typed info) where
  infoType = getType'

-- | Gets the type information of a value
getType :: TypeInfo info => Meta info a -> Type ()
getType = infoType . getInfo

-- | Adds type information to a value
withType :: Type () -> Meta info a -> Meta (Typed info) a
withType ty (x :&: info) = (x :&: info ::: ty)

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
  deriving Eq

instance Show ExprKind where
  show = \case
    KValue   -> "value"
    KPattern -> "pattern"
    KType    -> "type"
    KEffect  -> "effect"

-- | A transformation to be applied to an AST
data AfterMap m = AfterMap
  { aExpr :: MetaR Span Expr -> m (MetaR Span Expr)
    -- | A special case used for transforming a use expression
  , aUseExpr :: AfterMap m -> Meta Span UseModule -> MetaR Span Expr -> m (Expr Span)
    -- | Allow the introduction of local variables in expressions
  , aWithBindings :: forall a. [String] -> m a -> m a
  , aPattern :: MetaR Span Pattern -> m (MetaR Span Pattern)
  , aType :: MetaR Span Type -> m (MetaR Span Type)
  , aEffect :: Meta Span Effect -> m (Meta Span Effect)
    -- | Note that this function is called after the sub-effects are transformed
  , aEffectSet :: EffectSet Span -> m (EffectSet Span)
    -- | Transformations for 'Path' require an 'ExprKind' to indicate where they are being used
  , aPath :: ExprKind -> Meta Span Path -> m Path }

-- | A default transformation which does nothing
aDefault :: Monad m => AfterMap m
aDefault = AfterMap
  { aExpr = pure
  , aUseExpr = \m use expr -> EUse use <$> after m expr
  , aWithBindings = const id
  , aPattern = pure
  , aType = pure
  , aEffect = pure
  , aEffectSet = pure
  , aPath = const (pure . unmeta) }

-- | A class for anything that can be transformed with an 'AfterMap'
class After a where
  -- | Applies the transformation represented by the 'AfterMap'
  after :: Monad m => AfterMap m -> Meta Span a -> m (Meta Span a)

-- | Wrapper for 'aPath' that more closely matches the signature of 'after'
afterPath :: Monad m => AfterMap m -> ExprKind -> Meta Span Path -> m (Meta Span Path)
afterPath m k pathWithMeta = do
  path <- aPath m k pathWithMeta
  return (path <$ pathWithMeta)

-- | A wrapper around a set of 'Effect's
newtype EffectSet info = EffectSet
  { setEffects :: Set (Meta info Effect) }
  deriving (Ord, Eq)

instance After (EffectSet Span) where
  after m =
    mapM \effs -> do
      effs <- EffectSet <$> Set.fromList <$> mapM (after m) (Set.toAscList $ setEffects effs)
      aEffectSet m effs

instance Show (EffectSet info) where
  show EffectSet { setEffects }
    | Set.null setEffects = "Pure"
    | otherwise = intercalate " + " $ map (show . unmeta) $ Set.toAscList setEffects

-- | An empty @EffectSet@
emptyEffectSet :: EffectSet info
emptyEffectSet = EffectSet Set.empty

-- | An @EffectSet@ with a single element
singletonEffectSet :: Meta info Effect -> EffectSet info
singletonEffectSet = EffectSet . Set.singleton

-- | An effect that can occur in impure code
data Effect
  -- | A named effect
  = EffectNamed Path
  -- | A lowercase effect variable
  | EffectPoly String
  -- | An effect left blank to be inferred
  | EffectAnon AnonCount
  -- | A local variable's effect
  | EffectLocal AnonCount
  deriving (Ord, Eq)

instance After Effect where
  after m x = do
    x <- aEffect m x
    forM x \case
      EffectNamed path ->
        EffectNamed <$> aPath m KEffect (path <$ x)
      other ->
        return other

instance Show Effect where
  show = \case
    EffectNamed path -> show path
    EffectPoly name  -> name
    EffectAnon _     -> "_"
    EffectLocal anon -> "<local" ++ show anon ++ ">"

-- | Formats a string of |...| bracketed effects to add after a declaration
effectSuffix :: [MetaR info EffectSet] -> String
effectSuffix = effectSuffixStr . map (show . unmeta)

-- | Same as 'effectSuffix', but accepts strings instead
effectSuffixStr :: [String] -> String
effectSuffixStr = concatMap \effect ->
  " |" ++ effect ++ "|"

-- | A path specifying a single item or module to use
data UseModule
  -- | Use everything in this scope
  = UseAny
  -- | Use a named item and certain sub-items
  | UseModule (Meta Span Name) UseContents
  deriving Eq

instance Show UseModule where
  show = \case
    UseAny -> "_"
    UseModule name contents ->
      show name ++ show contents

-- | Specifies which sub-items to use in a 'UseModule'
data UseContents
  -- | Use a single sub-module separated by a dot
  = UseDot (Meta Span UseModule)
  -- | Use all of a list of items (use @[]@ to end use path)
  | UseAll [Meta Span UseModule]
  deriving Eq

instance Show UseContents where
  show = \case
    UseDot rest ->
      '.' : show rest
    UseAll [] ->
      ""
    UseAll rest ->
      " (" ++ intercalate ", " (map show rest) ++ ")"

-- | The type of an expression
data Type info
  -- | The @()@ type
  = TUnit
  -- | A named type and any effect arguments
  | TNamed [MetaR info EffectSet] (Meta info Path)
  -- | A lowercase type variable
  | TPoly String
  -- | A type left blank to be inferred
  | TAnon AnonCount
  -- | An application of a type argument to a type
  | TApp (MetaR info Type) (MetaR info Type)
  -- | A type with a universally quantified effect variable
  | TForEff (Meta info String) (MetaR info Type)

  -- Unassociated operators
  | TParen (MetaR info Type)
  | TUnaryOp (Meta info Path) (MetaR info Type)
  | TBinOp (Meta info Path) (MetaR info Type) (MetaR info Type)
  deriving (Eq)

instance After (Type Span) where
  after m x = do
    x <- aType m x
    forM x \case
      TNamed effs path ->
        TNamed <$> mapM (after m) effs <*> afterPath m KType path
      TApp a b ->
        TApp <$> after m a <*> after m b
      TForEff e ty ->
        TForEff e <$> aWithBindings m [unmeta e] (after m ty)
      TParen a ->
        TParen <$> after m a
      TUnaryOp path a ->
        TUnaryOp <$> afterPath m KType path <*> after m a
      TBinOp path a b -> do
        a <- after m a
        path <- afterPath m KType path
        b <- after m b
        return $ TBinOp path a b
      other ->
        return other

instance Show (Type info) where
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
    TForEff e ty ->
      "(|" ++ unmeta e ++ "| " ++ show ty ++ ")"
    TParen ty -> "{" ++ show ty ++ "}"
    TUnaryOp (Path { unpath = [Unary op] } :&: _) ty ->
      "{" ++ op ++ show ty ++ "}"
    TUnaryOp op ty ->
      "{" ++ show op ++ " " ++ show ty ++ "}"
    TBinOp (Path { unpath = [Operator op] } :&: _) lhs rhs ->
      "{" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ "}"
    TBinOp op lhs rhs ->
      "{" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ "}"

-- | A form of a 'Type' with all applications reduced
data ReducedApp = ReducedApp
  { reducedType :: MetaR Span Type
  , reducedArgs :: [MetaR Span Type] }

-- | Try to reduce all applications, otherwise return the conflicting infix operators
reduceApply :: MetaR Span Type -> Either (Meta Span Path, Meta Span Path) ReducedApp
reduceApply typeWithMeta =
  case unmeta typeWithMeta of
    TApp a b -> do
      ReducedApp ty args <- reduceApply a
      Right $ ReducedApp ty (args ++ [b])
    TParen ty ->
      reduceApply ty
    TUnaryOp a (TBinOp b _ _ :&: _) ->
      Left (a, b)
    TBinOp a _ (TBinOp b _ _ :&: _) ->
      Left (a, b)
    TUnaryOp path ty ->
      Right $ ReducedApp (copyInfo path $ TNamed [] path) [ty]
    TBinOp path a b ->
      Right $ ReducedApp (copyInfo path $ TNamed [] path) [a, b]
    _ ->
      Right $ ReducedApp typeWithMeta []

-- | Try to reduce all applications but don't allow infix operators
reduceApplyNoInfix :: MetaR Span Type -> Either (Meta Span Path) ReducedApp
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
findBase :: MetaR info Type -> (MetaR info Type, Int)
findBase = go 0
  where
    go n ty =
      case unmeta ty of
        TApp a _ ->
          go (n + 1) a
        _ ->
          (ty, n)

-- | Create a function type from a series of argument types and a return type
expandFunction :: DefaultInfo info => [MetaR info Type] -> MetaR info Type -> MetaR info Type
expandFunction [] ty = ty
expandFunction (ty:types) ret =
  (meta $ TNamed [] $ meta $ Core $ Operator "->") `app` ty `app` expandFunction types ret
  where
    app a b = meta $ TApp a b

-- | A function arrow with a list of effect parameters
pattern TAnyFuncArrow :: [MetaR info EffectSet] -> Type info
pattern TAnyFuncArrow effs <- TNamed effs (Core (Operator "->") :&: _)

-- | A function type with a list of effect parameters
pattern TAnyFunc :: [MetaR info EffectSet] -> MetaR info Type -> MetaR info Type -> Type info
pattern TAnyFunc effs a b <-
  TApp (TApp (TAnyFuncArrow effs :&: _) a :&: _) b

-- | A function type with a single effect parameter
pattern TEffFunc :: MetaR info EffectSet -> MetaR info Type -> MetaR info Type -> Type info
pattern TEffFunc eff a b <- TAnyFunc [eff] a b

-- | A function type with no effect parameters
pattern TFunc :: MetaR info Type -> MetaR info Type -> Type info
pattern TFunc a b <- TAnyFunc [] a b

-- | An effect representing pure code
pattern EffectPure :: Effect
pattern EffectPure = EffectNamed (Core (Identifier "Pure"))

-- | An effect representing an uncallable function
pattern EffectVoid :: Effect
pattern EffectVoid = EffectNamed (Core (Identifier "Void"))

-- | A concrete value produced by evaluating an expression
data Value info
  -- | The @()@ value
  = VUnit
  -- | A function value with match cases for its inputs
  | VFun [MatchCase info]
  -- | An evaluated data constructor
  | VDataCons Path [MetaR info Value]

instance Show (Value info) where
  show = \case
    VUnit -> "()"
    VFun cases ->
      "(fun" ++ showCases True cases ++ ")"
    VDataCons path [] ->
      show path
    VDataCons path vals ->
      "(" ++ show path ++ " " ++ intercalate " " (map show vals) ++ ")"

instance Eq (Value info) where
  VUnit == VUnit = True
  VFun c0 == VFun c1 =
    c0 == c1
  _ == _ = False

-- | A single case in a function or match expression
type MatchCase info = ([MetaR info Pattern], MetaR info Expr)

-- | Shows a set of match cases, optionally allowing them to be on one line if short
showCases :: Bool -> [MatchCase info] -> String
showCases True [c] = indent (showCase c)
showCases _ cases = "\n  " ++ intercalate "\n  " (map showCase cases)

-- | Shows a single match case
showCase :: MatchCase info -> String
showCase (pats, expr) = intercalate " " (map show pats) ++ " ->" ++ indent (show expr)

-- | An expression that can be used to produce a 'Value'
data Expr info
  -- | Lifts a 'Value' to be an expression
  = EValue (Value info)
  -- | A global binding for a value
  | EGlobal Path
  -- | A local value with an index and optional name
  | EIndex Int (Maybe String)
  -- | An application of an argument to a function
  | EApp (MetaR info Expr) (MetaR info Expr)
  -- | Evaluates one expression and returns the other
  | ESeq (MetaR info Expr) (MetaR info Expr)
  -- | Binds an expression to a pattern for its body
  | ELet (MetaR info Pattern) (MetaR info Expr) (MetaR info Expr)
  -- | Matches some expressions against some match cases
  | EMatchIn [MetaR info Expr] [MatchCase info]
  -- | Imports some values into scope for its body
  | EUse (Meta info UseModule) (MetaR info Expr)
  -- | Ascribes a type to an expression
  | ETypeAscribe (MetaR info Expr) (MetaR info Type)
  -- | The same as 'VDataCons' but for expressions
  | EDataCons Path [MetaR info Expr]

  -- Unassociated operators
  | EParen (MetaR info Expr)
  | EUnaryOp (Meta info Path) (MetaR info Expr)
  | EBinOp (Meta info Path) (MetaR info Expr) (MetaR info Expr)

instance After (Expr Span) where
  after m x = do
    x <- aExpr m x
    forM x \case
      EValue (VFun cases) ->
        EValue . VFun <$> afterCases cases
      EGlobal path ->
        EGlobal <$> aPath m KValue (path <$ x)
      EApp a b ->
        EApp <$> after m a <*> after m b
      ESeq a b ->
        ESeq <$> after m a <*> after m b
      ELet pat val expr -> do
        pat <- after m pat
        val <- after m val
        expr <- aWithBindings m (catMaybes $ bindingsForPat pat) $ after m expr
        return $ ELet pat val expr
      EMatchIn exprs cases ->
        EMatchIn <$> mapM (after m) exprs <*> afterCases cases
      EUse use a ->
        aUseExpr m m use a
      ETypeAscribe a ty ->
        ETypeAscribe <$> after m a <*> after m ty
      EDataCons path exprs -> do
        p <- aPath m KValue (path <$ x)
        s <- mapM (after m) exprs
        return $ EDataCons p s
      EParen a ->
        EParen <$> after m a
      EUnaryOp path a ->
        EUnaryOp <$> afterPath m KValue path <*> after m a
      EBinOp path a b -> do
        a <- after m a
        path <- afterPath m KValue path
        b <- after m b
        return $ EBinOp path a b
      other ->
        return other
    where
      afterCases =
        mapM \(pats, expr) -> do
          pats <- forM pats $ after m
          expr <- aWithBindings m (catMaybes $ concatMap bindingsForPat pats) $ after m expr
          return (pats, expr)

instance Eq (Expr info) where
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

instance Show (Expr info) where
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
    EUnaryOp (Path { unpath = [Unary op] } :&: _) expr ->
      "{" ++ op ++ show expr ++ "}"
    EUnaryOp op expr ->
      "{" ++ show op ++ " " ++ show expr ++ "}"
    EBinOp (Path { unpath = [Operator op] } :&: _) lhs rhs ->
      "{" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ "}"
    EBinOp op lhs rhs ->
      "{" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ "}"

-- | A pattern which can match a value and bind variables
data Pattern info
  -- | The @()@ pattern
  = PUnit
  -- | Matches anything and ignores it
  | PAny
  -- | Matches anything and creates a binding
  | PBind (Maybe String)
  -- | Tries to match a data type constructor
  | PCons (Meta Span Path) [MetaR info Pattern]
  -- | Ascribes a type to a pattern
  | PTypeAscribe (MetaR info Pattern) (MetaR info Type)

  -- Unassociated operators
  | PParen (MetaR info Pattern)
  | PUnaryOp (Meta info Path) (MetaR info Pattern)
  | PBinOp (Meta info Path) (MetaR info Pattern) (MetaR info Pattern)

instance After (Pattern Span) where
  after m x = do
    x <- aPattern m x
    forM x \case
      PCons path xs ->
        PCons <$> afterPath m KPattern path <*> mapM (after m) xs
      PTypeAscribe a ty ->
        PTypeAscribe <$> after m a <*> after m ty
      PParen a ->
        PParen <$> after m a
      PUnaryOp path a ->
        PUnaryOp <$> afterPath m KPattern path <*> after m a
      PBinOp path a b -> do
        a <- after m a
        path <- afterPath m KPattern path
        b <- after m b
        return $ PBinOp path a b
      other ->
        return other

instance Eq (Pattern info) where
  PUnit   == PUnit   = True
  PAny    == PAny    = True
  PBind _ == PBind _ = True
  PCons n0 l0 == PCons n1 l1 =
    n0 == n1 && l0 == l1
  PTypeAscribe p0 t0 == PTypeAscribe p1 t1 =
    p0 == p1 && t0 == t1
  -- PParen, PUnaryOp, and PBinOp are omitted as they will be removed by later passes
  _ == _ = False

instance Show (Pattern info) where
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
    PUnaryOp (Path { unpath = [Unary op] } :&: _) pat ->
      "{" ++ op ++ show pat ++ "}"
    PUnaryOp op pat ->
      "{" ++ show op ++ " " ++ show pat ++ "}"
    PBinOp (Path { unpath = [Operator op] } :&: _) lhs rhs ->
      "{" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ "}"
    PBinOp op lhs rhs ->
      "{" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ "}"

-- | Makes a list of all local variables created by the pattern
bindingsForPat :: MetaR info Pattern -> [Maybe String]
bindingsForPat pat =
  case unmeta pat of
    PUnit -> []
    PAny -> []
    PBind b -> [b]
    PCons _ pats ->
      pats >>= bindingsForPat
    PTypeAscribe pat _ ->
      bindingsForPat pat
    PParen pat ->
      bindingsForPat pat
    PUnaryOp _ pat ->
      bindingsForPat pat
    PBinOp _ lhs rhs ->
      bindingsForPat lhs ++ bindingsForPat rhs

-- | Assert that there are no duplicate bindings in a set of patterns
assertUniqueBindings :: (AddError m, SpanInfo info) => FilePath -> [MetaR info Pattern] -> m ()
assertUniqueBindings file pats =
  evalStateT (void $ runMaybeT $ mapM_ check pats) Set.empty
  where
    check patternWithMeta =
      case unmeta patternWithMeta of
        PBind (Just name) -> do
          s <- get
          if Set.member name s then
            MaybeT do
              addError compileError
                { errorFile = file
                , errorSpan = getSpan patternWithMeta
                , errorMessage =
                  "duplicate name binding not allowed in pattern" }
              return Nothing
          else
            put $ Set.insert name s
        PCons _ pats ->
          mapM_ check pats
        PTypeAscribe pat _ ->
          check pat
        PParen pat ->
          check pat
        PUnaryOp _ pat ->
          check pat
        PBinOp _ lhs rhs ->
          check lhs >> check rhs
        _ ->
          return ()

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
extractLocalPath (Path { unpath = [name] }) = extractLocalName name
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
  opNamed :: Meta Span Path -> a
  -- | Creates an expression in parentheses
  opParen :: Meta Span a -> a
  -- | Creates an expression with a unary operator
  opUnary :: Meta Span Path -> Meta Span a -> a
  -- | Creates an expression with a binary operator
  opBinary :: Meta Span Path -> Meta Span a -> Meta Span a -> a
  -- | Tries to create an application of two expressions
  opApply :: Meta Span a -> Meta Span a -> Either (Meta Span String) (a)

  -- | If sequencing is supported, create a sequence of two expressions
  opSeq :: Maybe (Meta Span a -> Meta Span a -> a)
  opSeq = Nothing

  -- | If effect application is supported, try to create an effect application
  opEffectApply :: Maybe (Meta Span a -> MetaR Span EffectSet -> Either (Meta Span String) (a))
  opEffectApply = Nothing

  -- | If effect application is supported, universally quantify an effect
  opForallEffect :: Maybe (Meta Span String -> Meta Span a -> a)
  opForallEffect = Nothing

instance ExprLike (Type Span) where
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
      effectApply (TNamed es path :&: _) e =
        Right $ TNamed (es ++ [e]) path
      effectApply _ e =
        Left $ copyInfo e "effect arguments can only occur immediately following a named type"
  opForallEffect = Just TForEff

instance ExprLike (Expr Span) where
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

instance ExprLike (Pattern Span) where
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
  opApply (PCons name xs :&: _) x =
    Right $ PCons name (xs ++ [x])
  opApply _ x =
    Left $ copyInfo x "pattern arguments can only occur immediately following a named pattern"

