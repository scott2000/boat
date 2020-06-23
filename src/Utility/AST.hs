-- | Defines everything related to the AST used to store parsed code
module Utility.AST
  ( -- * Metadata
    Meta
  , MetaR
  , MetaWith (..)
  , meta
  , metaWithSpan
  , copySpan
  , metaWithEnds
  , pattern DefaultMeta

    -- * Basic Expressions
  , ExprKind (..)
  , MatchCase
  , MatchCaseWith
  , Expr
  , ExprWith (..)
  , Value
  , ValueWith (..)
  , Pattern
  , PatternWith (..)
  , bindingsForPat
  , assertUniqueBindings
  , Type (..)
  , EffectSet (..)
  , emptyEffectSet
  , singletonEffectSet
  , Effect (..)
  , pattern EffectPure
  , pattern EffectVoid
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
import Data.Maybe
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

-- | Stores a value with optional span metadata
type Meta = MetaWith ()

-- | Helper for recursive versions of 'MetaWith'
type MetaR expr ty = MetaWith ty (expr ty)

-- | Stores a value with optional span metadata and some type information
data MetaWith ty a = Meta
  { -- | The inner value being stored
    unmeta :: a
    -- | The location of the value in its source file
  , metaSpan :: !(Maybe Span)
    -- | The type of a value (if inferred and applicable)
  , metaTy :: !ty }
  deriving (Functor, Foldable, Traversable)

instance (Ord ty, Ord a) => Ord (MetaWith ty a) where
  m0 `compare` m1 = unmeta m0 `compare` unmeta m1 <> metaTy m0 `compare` metaTy m1

instance (Eq ty, Eq a) => Eq (MetaWith ty a) where
  m0 == m1 = unmeta m0 == unmeta m1 && metaTy m0 == metaTy m1

instance Show a => Show (MetaWith ty a) where
  showsPrec i = showsPrec i . unmeta

-- | Stores a value with no additional metadata
meta :: a -> Meta a
meta x = Meta
  { unmeta = x
  , metaSpan = Nothing
  , metaTy = () }

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
  deriving Eq

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
    -- | Allow the introduction of local variables in expressions
  , aWithBindings :: forall a. [String] -> m a -> m a
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
  , aWithBindings = const id
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
    mapM \EffectSet { setEffects } ->
      EffectSet <$> Set.fromList <$> mapM (after m) (Set.toList setEffects)

instance Show EffectSet where
  show EffectSet { setEffects }
    | Set.null setEffects = "Pure"
    | otherwise = intercalate " + " $ map show $ Set.toList setEffects

emptyEffectSet :: EffectSet
emptyEffectSet = EffectSet Set.empty

singletonEffectSet :: Meta Effect -> EffectSet
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
  -- | A set of effects that are only present in both sets
  | EffectIntersection EffectSet EffectSet
  deriving (Ord, Eq)

instance After Effect where
  after m x = do
    x' <- aEffect m x
    forM x' \case
      EffectNamed path ->
        EffectNamed <$> aPath m KEffect (path <$ x')
      other ->
        return other

instance Show Effect where
  show = \case
    EffectNamed path -> show path
    EffectPoly name  -> name
    EffectAnon _     -> "_"
    EffectLocal anon -> "<local" ++ show anon ++ ">"
    EffectIntersection lhs rhs ->
      "(" ++ show lhs ++ ") & (" ++ show rhs ++ ")"

-- | Formats a string of |...| bracketed effects to add after a declaration
effectSuffix :: [Meta EffectSet] -> String
effectSuffix = effectSuffixStr . map show

-- | Same as 'effectSuffix', but accepts strings instead
effectSuffixStr :: [String] -> String
effectSuffixStr = concatMap \effect ->
  " |" ++ effect ++ "|"

-- | A constraint from a with-clause in a declaration
data Constraint
  = Meta Effect `IsSubEffectOf` EffectSet
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
  deriving Eq

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
data Type
  -- | The @()@ type
  = TUnit
  -- | A named type and any effect arguments
  | TNamed [Meta EffectSet] (Meta Path)
  -- | A lowercase type variable
  | TPoly String
  -- | A type left blank to be inferred
  | TAnon AnonCount
  -- | An application of a type argument to a type
  | TApp (Meta Type) (Meta Type)
  -- | A type with a universally quantified effect variable
  | TForEff (Meta String) (Meta Type)

  -- Unassociated operators
  | TParen (Meta Type)
  | TUnaryOp (Meta Path) (Meta Type)
  | TBinOp (Meta Path) (Meta Type) (Meta Type)
  deriving Eq

instance After Type where
  after m x = do
    x' <- aType m x
    forM x' \case
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
    TForEff e ty ->
      "(|" ++ unmeta e ++ "| " ++ show ty ++ ")"
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

-- | An effect representing an uncallable function
pattern EffectVoid :: Effect
pattern EffectVoid = EffectNamed (Core (Identifier "Void"))

-- | A concrete value produced by evaluating an expression
type Value = ValueWith ()

-- | A concrete value produced by evaluating an expression (with some type information)
data ValueWith ty
  -- | The @()@ value
  = VUnit
  -- | A function value with match cases for its inputs
  | VFun [MatchCaseWith ty]
  -- | An evaluated data constructor
  | VDataCons Path [ValueWith ty]

instance Show (ValueWith ty) where
  show = \case
    VUnit -> "()"
    VFun cases ->
      "(fun" ++ showCases True cases ++ ")"
    VDataCons path [] ->
      show path
    VDataCons path vals ->
      "(" ++ show path ++ " " ++ intercalate " " (map show vals) ++ ")"

instance Eq ty => Eq (ValueWith ty) where
  VUnit == VUnit = True
  VFun c0 == VFun c1 =
    c0 == c1
  _ == _ = False

-- | A single case in a function or match expression
type MatchCase = MatchCaseWith ()

-- | A single case in a function or match expression (with some type information)
type MatchCaseWith ty = ([Meta Pattern], MetaR ExprWith ty)

-- | Shows a set of match cases, optionally allowing them to be on one line if short
showCases :: Bool -> [MatchCaseWith ty] -> String
showCases True [c] = indent (showCase c)
showCases _ cases = "\n  " ++ intercalate "\n  " (map showCase cases)

-- | Shows a single match case
showCase :: MatchCaseWith ty -> String
showCase (pats, expr) = intercalate " " (map show pats) ++ " ->" ++ indent (show expr)

-- | An expression that can be used to produce a 'Value'
type Expr = ExprWith ()

-- | An expression that can be used to produce a 'Value' (with some type information)
data ExprWith ty
  -- | Lifts a 'Value' to be an expression
  = EValue (ValueWith ty)
  -- | A global binding for a value
  | EGlobal Path
  -- | A local value with an index and optional name
  | EIndex Int (Maybe String)
  -- | An application of an argument to a function
  | EApp (MetaR ExprWith ty) (MetaR ExprWith ty)
  -- | Evaluates one expression and returns the other
  | ESeq (MetaR ExprWith ty) (MetaR ExprWith ty)
  -- | Binds an expression to a pattern for its body
  | ELet (Meta Pattern) (MetaR ExprWith ty) (MetaR ExprWith ty)
  -- | Matches some expressions against some match cases
  | EMatchIn [MetaR ExprWith ty] [MatchCaseWith ty]
  -- | Imports some values into scope for its body
  | EUse (Meta UseModule) (MetaR ExprWith ty)
  -- | Ascribes a type to an expression
  | ETypeAscribe (MetaR ExprWith ty) (Meta Type)
  -- | The same as 'VDataCons' but for expressions
  | EDataCons Path [MetaR ExprWith ty]

  -- Unassociated operators
  | EParen (MetaR ExprWith ty)
  | EUnaryOp (Meta Path) (MetaR ExprWith ty)
  | EBinOp (Meta Path) (MetaR ExprWith ty) (MetaR ExprWith ty)

instance After Expr where
  after m x = do
    x' <- aExpr m x
    forM x' \case
      EValue (VFun cases) ->
        EValue . VFun <$> afterCases cases
      EGlobal path ->
        EGlobal <$> aPath m KValue (path <$ x')
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
        mapM \(pats, expr) -> do
          pats <- forM pats $ after m
          expr <- aWithBindings m (catMaybes $ concatMap bindingsForPat pats) $ after m expr
          return (pats, expr)

instance Eq ty => Eq (ExprWith ty) where
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

instance Show (ExprWith ty) where
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
type Pattern = PatternWith ()

-- | A pattern which can match a value and bind variables (with some type information)
data PatternWith ty
  -- | The @()@ pattern
  = PUnit
  -- | Matches anything and ignores it
  | PAny
  -- | Matches anything and creates a binding
  | PBind (Maybe String)
  -- | Tries to match a data type constructor
  | PCons (Meta Path) [MetaR PatternWith ty]
  -- | Ascribes a type to a pattern
  | PTypeAscribe (MetaR PatternWith ty) (Meta Type)

  -- Unassociated operators
  | PParen (MetaR PatternWith ty)
  | PUnaryOp (Meta Path) (MetaR PatternWith ty)
  | PBinOp (Meta Path) (MetaR PatternWith ty) (MetaR PatternWith ty)

instance After Pattern where
  after m x = do
    x' <- aPattern m x
    forM x' \case
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

instance Eq ty => Eq (PatternWith ty) where
  PUnit   == PUnit   = True
  PAny    == PAny    = True
  PBind _ == PBind _ = True
  PCons n0 l0 == PCons n1 l1 =
    n0 == n1 && l0 == l1
  PTypeAscribe p0 t0 == PTypeAscribe p1 t1 =
    p0 == p1 && t0 == t1
  -- PParen, PUnaryOp, and PBinOp are omitted as they will be removed by later passes
  _ == _ = False

instance Show (PatternWith ty) where
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
assertUniqueBindings :: AddError m => FilePath -> [Meta Pattern] -> m ()
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
                { errorFile = Just file
                , errorSpan = metaSpan patternWithMeta
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

  -- | If effect application is supported, universally quantify an effect
  opForallEffect :: Maybe (Meta String -> Meta a -> a)
  opForallEffect = Nothing

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
  opForallEffect = Just TForEff

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

