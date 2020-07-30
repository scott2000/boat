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
  , Unassociated (..)
  , MatchCase
  , Expr (..)
  , Value (..)
  , Pattern (..)
  , bindingsForPat
  , assertUniqueBindings
  , Type (..)
  , findBlank
  , Effect (..)
  , pattern EffectPure
  , pattern EffectVoid
  , NoCmp (..)
  , EffectSet (..)
  , esEmpty
  , esSingleton
  , esSize
  , esInsert
  , esMember
  , esDelete
  , esLookup
  , esHideInfo
  , esToList
  , toUniqueEffectSet
  , UseModule (..)
  , UseContents (..)

    -- * Functions and Type Applications
  , ReducedApp (..)
  , tryReduceApply
  , reduceApplyNoInfix
  , findBase
  , expandFunction
  , expandApp
  , pattern TFuncArrow
  , pattern TFunc
  , pattern TEffFunc

    -- * Parsing and Modifying Expressions
  , Of (..)
  , ExprLike (..)
  , After (..)
  , afterPath
  , AfterMap (..)
  , aDefault
  , ShowExpr (..)
  , showExprBlock
  , showExprNoSpace
  , newline

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

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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
  infoFile :: info -> File

-- | Adds file information to a value (usually a 'Span')
data InFile info = (:/:)
  { -- | The file path where the item can be found
    getFile' :: !File
    -- | The rest of the information
  , unfile :: !info }
  deriving (Ord, Eq)

instance SpanInfo info => SpanInfo (InFile info) where
  infoSpan = infoSpan . unfile

instance DefaultInfo info => DefaultInfo (InFile info) where
  defaultInfo = NoFile :/: defaultInfo

instance FileInfo (InFile info) where
  infoFile = getFile'

instance TypeInfo info => TypeInfo (InFile info) where
  infoType = infoType . unfile

-- | Gets the file information of a value
getFile :: FileInfo info => Meta info a -> File
getFile = infoFile . getInfo

-- | Adds file information to a value
withFile :: File -> Meta info a -> Meta (InFile info) a
withFile file (x :&: info) = (x :&: file :/: info)

-- | Metadata that contains type information
class TypeInfo info where
  -- | Extracts the type information
  infoType :: info -> MetaR () Type

-- | Adds type information to a value
data Typed info = (:::)
  { -- | The rest of the information
    untype :: !info
    -- | The type of the item
  , getType' :: !(MetaR () Type) }

instance SpanInfo info => SpanInfo (Typed info) where
  infoSpan = infoSpan . untype

instance FileInfo info => FileInfo (Typed info) where
  infoFile = infoFile . untype

instance TypeInfo (Typed info) where
  infoType = getType'

-- | Gets the type information of a value
getType :: TypeInfo info => Meta info a -> MetaR () Type
getType = infoType . getInfo

-- | Adds type information to a value
withType :: MetaR () Type -> Meta info a -> Meta (Typed info) a
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
  , aPoly :: ExprKind -> Meta Span String -> m String
  , aPath :: ExprKind -> Meta Span Path -> m Path
  , aEffectSet :: Maybe ([Meta Span Effect] -> m (EffectSet Span)) }

-- | A default transformation which does nothing
aDefault :: Monad m => AfterMap m
aDefault = AfterMap
  { aExpr = pure
  , aUseExpr = \m use expr -> EUse use <$> after m expr
  , aWithBindings = const id
  , aPattern = pure
  , aType = pure
  , aPoly = const (pure . unmeta)
  , aPath = const (pure . unmeta)
  , aEffectSet = Nothing }

-- | A class for anything that can be transformed with an 'AfterMap'
class After a where
  -- | Applies the transformation represented by the 'AfterMap'
  after :: Monad m => AfterMap m -> Meta Span a -> m (Meta Span a)
  incomplete :: Meta Span a

-- | Wrapper for 'aPath' that more closely matches the signature of 'after'
afterPath :: Monad m => AfterMap m -> ExprKind -> Meta Span Path -> m (Meta Span Path)
afterPath m k pathWithMeta = do
  path <- aPath m k pathWithMeta
  return $ copyInfo pathWithMeta path

-- | Like 'Show', but provides additional information about precedence and indentation
class ShowExpr a where
  -- | Returns true if the expression is just a name
  isSimple :: a -> Bool
  -- | Formats the expression given the current precedence and indentation level
  showExpr :: Prec -> Int -> a -> String

instance ShowExpr a => ShowExpr (Meta info a) where
  isSimple = isSimple . unmeta
  showExpr prec indent = showExpr prec indent . unmeta

instance ShowExpr String where
  isSimple = const True
  showExpr = const $ const id

-- | Show an expression block with no parentheses at the outermost level
showExprBlock :: ShowExpr a => Int -> a -> String
showExprBlock = showExpr ExpectEndPrec

-- | Show an expression with parentheses around any applications
showExprNoSpace :: ShowExpr a => Int -> a -> String
showExprNoSpace = showExpr ApplyPrec

-- | Add a newline with a certain indentation level
newline :: Int -> String
newline indent = '\n' : replicate indent ' '

-- | Automatically surround an indented block in parentheses
parenBlock :: Prec -> Int -> (Int -> String) -> String
parenBlock prec indent f
  | prec < MinPrec = f indent
  | otherwise =
    let indent' = indent + indentationIncrement in
    "(" ++ newline indent' ++ f indent' ++ ")"

-- | Automatically surround a function application in parentheses
parenApp :: (ShowExpr a, ShowExpr b) => Prec -> Int -> a -> b -> String
parenApp prec indent a b
  | prec < ApplyPrec = normal
  | otherwise =
    "(" ++ normal ++ ")"
  where
    normal = showExpr NormalPrec indent a ++ " " ++ showExpr ApplyPrec indent b

-- | Automatically surround a unary operator in parentheses
parenUnary :: ShowExpr a => Prec -> Int -> String -> a -> String
parenUnary prec indent op ty
  | prec < CompactPrec = normal
  | otherwise =
    "(" ++ normal ++ ")"
  where
    normal =
      op ++ " " ++ showExpr CompactPrec indent ty

-- | Automatically surround an infix operator in parentheses
parenInfix :: ShowExpr a => Prec -> Int -> a -> String -> a -> String
parenInfix prec indent a op b
  | prec < NormalPrec = normal
  | prec < CompactPrec, isSimple a, isSimple b =
    showExpr CompactPrec indent a ++ op ++ showExpr CompactPrec indent b
  | otherwise =
    "(" ++ normal ++ ")"
  where
    normal =
      showExpr NormalPrec indent a ++ " " ++ op ++ " " ++ showExpr NormalPrec indent b

-- | Automatically surround a special operator in parentheses
parenSpecial :: (ShowExpr a, ShowExpr b) => Prec -> Int -> a -> String -> b -> String
parenSpecial prec indent a op b
  | prec < SpecialPrec = normal
  | otherwise =
    "(" ++ normal ++ ")"
  where
    normal =
      showExpr SpecialPrec indent a ++ " " ++ op ++ " " ++ showExpr MinPrec indent b

-- | A type containing an unassociated operator expression
data Unassociated info a
  = UParen
    { uOp :: (Meta info a) }
  | UUnaryOp
    { uOp :: (Meta info a)
    , uRhs :: (Meta info a) }
  | UBinOp
    { uOp :: (Meta info a)
    , uLhs :: (Meta info a)
    , uRhs :: (Meta info a) }
  deriving Eq

instance ShowExpr a => ShowExpr (Unassociated info a) where
  isSimple = const False
  showExpr _ indent = \case
    UParen op ->
      "{" ++ showExprBlock indent op ++ "}"
    UUnaryOp op rhs ->
      "{" ++ showExprNoSpace indent op ++ " " ++ showExprNoSpace indent rhs ++ "}"
    UBinOp op lhs rhs ->
      "{" ++ showExprNoSpace indent lhs ++
      " `" ++ showExprNoSpace indent op ++
      "` " ++ showExprNoSpace indent rhs ++ "}"

-- | Calls 'after' on the expressions contained in the 'Unassociated'
afterUnassociated :: (After a, Monad m) => AfterMap m -> Unassociated Span a -> m (Unassociated Span a)
afterUnassociated m = \case
  UParen op ->
    UParen <$> after m op
  UUnaryOp op rhs ->
    UUnaryOp <$> after m op <*> after m rhs
  UBinOp op lhs rhs ->
    UBinOp <$> after m op <*> after m lhs <*> after m rhs

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
  after m x =
    forM x \case
      EffectNamed path ->
        EffectNamed <$> aPath m KEffect (copyInfo x path)
      EffectPoly name ->
        EffectPoly <$> aPoly m KEffect (copyInfo x name)
      other ->
        return other

  incomplete = meta $ EffectNamed Incomplete

instance Show Effect where
  show = \case
    EffectNamed path -> show path
    EffectPoly name  -> name
    EffectAnon _     -> "_"
    EffectLocal anon -> "<local" ++ show anon ++ ">"

-- | An effect representing pure code
pattern EffectPure :: Path
pattern EffectPure = Core (Identifier "Pure")

-- | An effect representing an uncallable function
pattern EffectVoid :: Path
pattern EffectVoid = Core (Identifier "Void")

-- | Always compares as equal no matter what value it holds
newtype NoCmp info = NoCmp
  { getNoCmp :: info }

instance Ord (NoCmp info) where
  _ `compare` _ = EQ

instance Eq (NoCmp info) where
  _ == _ = True

-- | A set of effects, splitting each kind of effect into a different map
data EffectSet info = EffectSet
  { esNamed :: !(HashMap Path (NoCmp info))
  , esPoly :: !(HashMap String (NoCmp info))
  , esAnon :: !(Map AnonCount (NoCmp info))
  , esLocal :: !(Map AnonCount (NoCmp info)) }
  deriving Eq

instance After (EffectSet Span) where
  after m x =
    case aEffectSet m of
      Nothing ->
        return x
      Just toEffectSet ->
        forM x \es ->
          mapM (after m) (esToList es) >>= toEffectSet

  incomplete = meta $ esSingleton $ incomplete

instance Show (EffectSet info) where
  show effs =
    case esToList effs of
      [] -> "Pure"
      es ->
        intercalate " + " $ map (show . unmeta) es

-- | An empty 'EffectSet'
esEmpty :: EffectSet info
esEmpty = EffectSet
  { esNamed = HashMap.empty
  , esPoly = HashMap.empty
  , esAnon = Map.empty
  , esLocal = Map.empty }

-- | An 'EffectSet' with a single element
esSingleton :: Meta info Effect -> EffectSet info
esSingleton eff = esInsert eff esEmpty

-- | Computes the total number of effects in an 'EffectSet'
esSize :: EffectSet info -> Int
esSize es =
  (HashMap.size $ esNamed es)
  + (HashMap.size $ esPoly es)
  + (Map.size $ esAnon es)
  + (Map.size $ esLocal es)

-- | Insert an 'Effect' into an 'EffectSet'
esInsert :: Meta info Effect -> EffectSet info -> EffectSet info
esInsert (eff :&: span) es =
  let span' = NoCmp span in
  case eff of
    EffectNamed name ->
      es { esNamed = HashMap.insert name span' $ esNamed es }
    EffectPoly name ->
      es { esPoly = HashMap.insert name span' $ esPoly es }
    EffectAnon anon ->
      es { esAnon = Map.insert anon span' $ esAnon es }
    EffectLocal anon ->
      es { esLocal = Map.insert anon span' $ esLocal es }

-- | Check if an 'Effect' is present in this 'EffectSet'
esMember :: Effect -> EffectSet info -> Bool
esMember eff es =
  case eff of
    EffectNamed name ->
      name `HashMap.member` esNamed es
    EffectPoly name ->
      name `HashMap.member` esPoly es
    EffectAnon anon ->
      anon `Map.member` esAnon es
    EffectLocal anon ->
      anon `Map.member` esLocal es

-- | Delete an 'Effect' from an 'EffectSet'
esDelete :: Effect -> EffectSet info -> EffectSet info
esDelete eff es =
  case eff of
    EffectNamed name ->
      es { esNamed = HashMap.delete name $ esNamed es }
    EffectPoly name ->
      es { esPoly = HashMap.delete name $ esPoly es }
    EffectAnon anon ->
      es { esAnon = Map.delete anon $ esAnon es }
    EffectLocal anon ->
      es { esLocal = Map.delete anon $ esLocal es }

-- | Get the information associated with an 'Effect' in an 'EffectSet', if it is present
esLookup :: Effect -> EffectSet info -> Maybe info
esLookup eff es =
  getNoCmp <$> case eff of
    EffectNamed name ->
      HashMap.lookup name $ esNamed es
    EffectPoly name ->
      HashMap.lookup name $ esPoly es
    EffectAnon anon ->
      Map.lookup anon $ esAnon es
    EffectLocal anon ->
      Map.lookup anon $ esLocal es

-- | Hide the information associated with each item in the 'EffectSet' by replacing it with @()@
esHideInfo :: EffectSet info -> EffectSet ()
esHideInfo es = EffectSet
  { esNamed = HashMap.map hide $ esNamed es
  , esPoly = HashMap.map hide $ esPoly es
  , esAnon = Map.map hide $ esAnon es
  , esLocal = Map.map hide $ esLocal es }
  where
    hide = const $ NoCmp ()

-- | Create a list of effects present in an 'EffectSet'
esToList :: EffectSet info -> [Meta info Effect]
esToList EffectSet { esNamed, esPoly, esAnon, esLocal } =
  let
    insertLocal = Map.foldrWithKey (insert EffectLocal) [] esLocal
    insertAnon = Map.foldrWithKey (insert EffectAnon) insertLocal esAnon
    insertPoly = HashMap.foldrWithKey (insert EffectPoly) insertAnon esPoly
  in
    HashMap.foldrWithKey (insert EffectNamed) insertPoly esNamed
  where
    insert f k (NoCmp v) list = (f k :&: v) : list

-- | Convert a list of effects to an 'EffectSet', giving an warning for duplicate effects
toUniqueEffectSet :: AddError m => File -> [Meta Span Effect] -> m (EffectSet Span)
toUniqueEffectSet file = go esEmpty
  where
    go es [] =
      let EffectSet { esNamed } = es in
      case HashMap.lookup EffectVoid esNamed of
        Just (NoCmp voidSpan) -> do
          -- If there is a `Void` effect, emit a warning for all other effects and just return `Void`
          let
            err = compileError
              { errorFile = file
              , errorKind = Warning
              , errorMessage = "effect is unnecessary since `Void` includes all effects" }
          forM_ (esToList es) \(eff :&: errorSpan) ->
            when (eff /= EffectNamed EffectVoid) $ addError err { errorSpan }
          return $ esSingleton $ EffectNamed EffectVoid :&: voidSpan
        Nothing ->
          case HashMap.lookup EffectPure esNamed of
            Just (NoCmp pureSpan) -> do
              -- If there is a `Pure` effect, remove it from the set and emit a warning if it was unnecessary
              when (esSize es > 1) do
                addError compileError
                  { errorFile = file
                  , errorSpan = pureSpan
                  , errorKind = Warning
                  , errorMessage = "effect `Pure` does nothing since there are other effects" }
              return es { esNamed = HashMap.delete EffectPure esNamed }
            Nothing ->
              return es
    go es (new:rest) =
      case esLookup (unmeta new) es of
        Nothing ->
          go (esInsert new es) rest
        Just oldSpan -> do
          let
            newSpan = getSpan new
            -- Make sure the warning isn't emitted for the first effect, even if the list is out of order
            (es', span)
              | newSpan < oldSpan = (esInsert new es, oldSpan)
              | otherwise         = (es, newSpan)
          addError compileError
            { errorFile = file
            , errorSpan = span
            , errorKind = Warning
            , errorMessage = "effect is unnecessary since it was already listed" }
          go es' rest

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
  -- | A named type
  | TNamed Path
  -- | A lowercase type variable
  | TPoly String
  -- | A type left blank to be inferred
  | TAnon AnonCount
  -- | An application of a type argument to a type
  | TApp (MetaR info Type) (MetaR info Type)
  -- | An application of an effect argument to a type
  | TEffApp (MetaR info Type) (MetaR info EffectSet)
  -- | A type with a universally quantified effect variable
  | TForEff (Meta info String) (MetaR info Type)
  -- | An unassociated operator expression
  | TUnassociated (Unassociated info (Type info))
  deriving Eq

instance After (Type Span) where
  after m x = do
    x <- aType m x
    forM x \case
      TNamed path ->
        TNamed <$> aPath m KType (copyInfo x path)
      TPoly name ->
        TPoly <$> aPoly m KType (copyInfo x name)
      TApp a b ->
        TApp <$> after m a <*> after m b
      TEffApp ty e ->
        TEffApp <$> after m ty <*> after m e
      TForEff e ty ->
        TForEff e <$> aWithBindings m [unmeta e] (after m ty)
      TUnassociated u ->
        TUnassociated <$> afterUnassociated m u
      other ->
        return other

  incomplete = meta $ TNamed Incomplete

instance ShowExpr (Type info) where
  isSimple = \case
    TUnit -> True
    TNamed _ -> True
    TPoly _ -> True
    TAnon _ -> True
    _ -> False

  showExpr prec indent = \case
    TUnit -> "()"
    TNamed path -> show path
    TPoly name -> name
    TAnon _ -> "_"
    TEffFunc a effs b ->
      parenSpecial prec indent a ("-|" ++ show effs ++ "|>") b
    TFunc a b ->
      parenSpecial prec indent a "->" b
    TApp (TNamed path :&: _) ty | Unary op <- last $ unpath path ->
      parenUnary prec indent op ty
    TApp (TApp (TNamed path :&: _) a :&: _) b | Operator op <- last $ unpath path ->
      parenInfix prec indent a op b
    TApp a b ->
      parenApp prec indent a b
    TEffApp ty e ->
      parenApp prec indent ty ("|" ++ show e ++ "|")
    TForEff e ty ->
      "(|" ++ unmeta e ++ "| " ++ show ty ++ ")"
    TUnassociated u ->
      showExpr prec indent u

instance Show (Type info) where
  show = showExprBlock 0

-- | Find the span of a 'TAnon' or 'EffectAnon' in the type if there is one
findBlank :: MetaR Span Type -> Maybe Span
findBlank (ty :&: span) =
  case ty of
    TAnon _ ->
      Just span
    TApp a b ->
      findBlank a <|> findBlank b
    TEffApp ty e ->
      findBlank ty <|> foldr (<|>) Nothing (map findBlankEff $ esToList $ unmeta e)
    TForEff _ ty ->
      findBlank ty
    TUnassociated (UParen op) ->
      findBlank op
    TUnassociated (UUnaryOp op rhs) ->
      findBlank op <|> findBlank rhs
    TUnassociated (UBinOp op lhs rhs) ->
      findBlank op <|> findBlank lhs <|> findBlank rhs
    _ ->
      Nothing
  where
    findBlankEff (eff :&: span) =
      case eff of
        EffectAnon _ ->
          Just span
        _ ->
          Nothing

-- | A form of a 'Type' with all applications reduced
data ReducedApp info = ReducedApp
  { reducedType :: MetaR info Type
  , reducedEffs :: [MetaR info EffectSet]
  , reducedArgs :: [MetaR info Type] }

-- | Try to reduce all applications, otherwise return the conflicting infix operators
tryReduceApply :: MetaR info Type -> Either (MetaR info Type, MetaR info Type) (ReducedApp info)
tryReduceApply typeWithMeta =
  case unmeta typeWithMeta of
    TApp a b -> do
      ReducedApp base effs args <- tryReduceApply a
      Right $ ReducedApp base effs (args ++ [b])
    TEffApp ty e -> do
      ReducedApp base effs args <- tryReduceApply ty
      Right $ ReducedApp base (effs ++ [e]) args
    TUnassociated (UParen ty) ->
      tryReduceApply ty
    TUnassociated (UUnaryOp a (TUnassociated (UBinOp b _ _) :&: _)) ->
      Left (a, b)
    TUnassociated (UBinOp a _ (TUnassociated (UBinOp b _ _) :&: _)) ->
      Left (a, b)
    TUnassociated (UUnaryOp op rhs) ->
      Right $ ReducedApp op [] [rhs]
    TUnassociated (UBinOp op lhs rhs) ->
      Right $ ReducedApp op [] [lhs, rhs]
    _ ->
      Right $ ReducedApp typeWithMeta [] []

-- | Try to reduce all applications but don't allow infix operators
reduceApplyNoInfix :: MetaR info Type -> Either (MetaR info Type) (ReducedApp info)
reduceApplyNoInfix typeWithMeta =
  case unmeta typeWithMeta of
    TApp a b -> do
      ReducedApp base effs args <- reduceApplyNoInfix a
      Right $ ReducedApp base effs (args ++ [b])
    TEffApp ty e -> do
      ReducedApp base effs args <- reduceApplyNoInfix ty
      Right $ ReducedApp base (effs ++ [e]) args
    TUnassociated (UParen ty) ->
      reduceApplyNoInfix ty
    TUnassociated (UUnaryOp op _) ->
      Left op
    TUnassociated (UBinOp op _ _) ->
      Left op
    _ ->
      Right $ ReducedApp typeWithMeta [] []

-- | Find the base of a series of applications and the number of applications removed
findBase :: MetaR info Type -> (MetaR info Type, Int, Int)
findBase = go 0 0
  where
    go numEffs numArgs ty =
      case unmeta ty of
        TApp a _ ->
          go numEffs (numArgs + 1) a
        TEffApp ty _ ->
          go (numEffs + 1) numArgs ty
        _ ->
          (ty, numEffs, numArgs)

-- | Create a function type from a series of argument types and a return type
expandFunction :: DefaultInfo info => [MetaR info Type] -> MetaR info Type -> MetaR info Type
expandFunction [] ty = ty
expandFunction (ty:types) ret =
  expandApp (meta TFuncArrow) [] [ty, expandFunction types ret]

-- | Create a type application from effect and type arguments and a base type
expandApp :: DefaultInfo info => MetaR info Type -> [MetaR info EffectSet] -> [MetaR info Type] -> MetaR info Type
expandApp base effs args =
  foldl' expandArg (foldl' expandEff base effs) args
  where
    expandEff ty e = meta $ TEffApp ty e
    expandArg a b = meta $ TApp a b

-- | The named type @Core.(->)@
pattern TFuncArrow :: Type info
pattern TFuncArrow = TNamed (Core (Operator "->"))

-- | A function type with no effect parameter
pattern TFunc :: MetaR info Type -> MetaR info Type -> Type info
pattern TFunc a b <-
  TApp (TApp (TFuncArrow :&: _) a :&: _) b

-- | A function type with a single effect parameter
pattern TEffFunc :: MetaR info Type -> MetaR info EffectSet -> MetaR info Type -> Type info
pattern TEffFunc a eff b <-
  TApp (TEffApp (TApp (TFuncArrow :&: _) a :&: _) eff :&: _) b

-- | A concrete value produced by evaluating an expression
data Value info
  -- | The @()@ value
  = VUnit
  -- | A function value with match cases for its inputs
  | VFun [MatchCase info]
  -- | An evaluated data constructor
  | VDataCons Path [MetaR info Value]

instance Eq (Value info) where
  VUnit == VUnit = True
  VFun c0 == VFun c1 =
    c0 == c1
  _ == _ = False

instance ShowExpr (Value info) where
  isSimple = \case
    VUnit -> True
    VDataCons _ [] -> True
    _ -> False

  showExpr prec indent = \case
    VUnit -> "()"
    VFun cases ->
      parenBlock prec indent \indent ->
        let indent' = indent + indentationIncrement in
        "fun" ++ newline indent'
        ++ showExprBlock indent' cases
    VDataCons path [] ->
      show path
    VDataCons path vals ->
      "(" ++ show path ++ " " ++ intercalate " " (map show vals) ++ ")"

instance Show (Value info) where
  show = showExprBlock 0

-- | A single case in a function or match expression
type MatchCase info = ([MetaR info Pattern], MetaR info Expr)

instance ShowExpr (MatchCase info) where
  isSimple = const False
  showExpr _ indent (pats, expr) =
    let indent' = indent + indentationIncrement in
    intercalate " " (map (showExprNoSpace indent) pats) ++ " ->"
    ++ newline indent'
    ++ showExprBlock indent' expr

instance ShowExpr [MatchCase info] where
  isSimple = const False
  showExpr prec indent =
    intercalate (newline indent) . map (showExpr prec indent)

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
  -- | An unassociated operator expression
  | EUnassociated (Unassociated info (Expr info))

instance After (Expr Span) where
  after m x = do
    x <- aExpr m x
    forM x \case
      EValue (VFun cases) ->
        EValue . VFun <$> afterCases cases
      EGlobal path ->
        EGlobal <$> aPath m KValue (copyInfo x path)
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
        p <- aPath m KValue $ copyInfo x path
        s <- mapM (after m) exprs
        return $ EDataCons p s
      EUnassociated u ->
        EUnassociated <$> afterUnassociated m u
      other ->
        return other
    where
      afterCases =
        mapM \(pats, expr) -> do
          pats <- forM pats $ after m
          expr <- aWithBindings m (catMaybes $ concatMap bindingsForPat pats) $ after m expr
          return (pats, expr)

  incomplete = meta $ EGlobal Incomplete

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

instance ShowExpr (Expr info) where
  isSimple = \case
    EValue val -> isSimple val
    EGlobal Path { unpath = [_] } -> True
    EIndex _ (Just _) -> True
    _ -> False

  showExpr prec indent = \case
    EValue val ->
      showExpr prec indent val
    EGlobal name -> show name
    EIndex 0 Nothing -> "?"
    EIndex n Nothing -> "?" ++ show n
    EIndex _ (Just name) -> name
    EApp (EGlobal path :&: _) ty | Unary op <- last $ unpath path ->
      parenUnary prec indent op ty
    EApp (EApp (EGlobal path :&: _) a :&: _) b | Operator op <- last $ unpath path ->
      parenInfix prec indent a op b
    EApp a b ->
      parenApp prec indent a b
    ESeq a b ->
      parenBlock prec indent \indent' ->
        showExprBlock indent' a
        ++ newline indent'
        ++ showExprBlock indent' b
    ELet p v e ->
      parenBlock prec indent \indent ->
        let indent' = indent + indentationIncrement in
        "let " ++ showExpr MinPrec indent p ++ " ="
        ++ newline indent'
        ++ showExprBlock indent' v
        ++ newline indent
        ++ showExprBlock indent e
    EMatchIn exprs cases ->
      parenBlock prec indent \indent ->
        let indent' = indent + indentationIncrement in
        "match " ++ intercalate " " (map (showExprNoSpace indent) exprs)
        ++ newline indent'
        ++ showExprBlock indent' cases
    EUse u e ->
      parenBlock prec indent \indent ->
        "use " ++ show u
        ++ newline indent
        ++ showExprBlock indent e ++ ""
    ETypeAscribe expr ty ->
      parenSpecial prec indent expr ":" ty
    EDataCons path [] ->
      show path
    EDataCons path exprs ->
      "(" ++ show path ++ " " ++ intercalate " " (map show exprs) ++ ")"
    EUnassociated u ->
      showExpr prec indent u

instance Show (Expr info) where
  show = showExprBlock 0

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
  -- | An unassociated operator expression
  | PUnassociated (Unassociated info (Pattern info))

instance After (Pattern Span) where
  after m x = do
    x <- aPattern m x
    forM x \case
      PCons path xs ->
        PCons <$> afterPath m KPattern path <*> mapM (after m) xs
      PTypeAscribe a ty ->
        PTypeAscribe <$> after m a <*> after m ty
      PUnassociated u ->
        PUnassociated <$> afterUnassociated m u
      other ->
        return other

  incomplete = meta $ PCons (meta Incomplete) []

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

instance ShowExpr (Pattern info) where
  isSimple = \case
    PUnit -> True
    PAny -> True
    PBind (Just _) -> True
    PCons _ [] -> True
    _ -> False

  showExpr prec indent = \case
    PUnit -> "()"
    PAny -> "_"
    PBind Nothing -> "?"
    PBind (Just name) -> name
    PCons path [ty] | Unary op <- last $ unpath $ unmeta path ->
      parenUnary prec indent op ty
    PCons path [a, b] | Operator op <- last $ unpath $ unmeta path ->
      parenInfix prec indent a op b
    PCons name [] -> show name
    PCons name pats ->
      "(" ++ show name ++ " " ++ intercalate " " (map show pats) ++ ")"
    PTypeAscribe pat ty ->
      "(" ++ show pat ++ " : " ++ show ty ++ ")"
    PUnassociated u ->
      showExpr prec indent u

instance Show (Pattern info) where
  show = showExprBlock 0

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
    PUnassociated (UParen op) ->
      bindingsForPat op
    PUnassociated (UUnaryOp _ rhs) ->
      bindingsForPat rhs
    PUnassociated (UBinOp _ lhs rhs) ->
      bindingsForPat lhs ++ bindingsForPat rhs

-- | Assert that there are no duplicate bindings in a set of patterns
assertUniqueBindings :: (AddError m, SpanInfo info) => File -> [MetaR info Pattern] -> m ()
assertUniqueBindings file pats =
  evalStateT (void $ runMaybeT $ mapM_ check pats) Set.empty
  where
    check patternWithMeta =
      case unmeta patternWithMeta of
        PBind (Just name) -> do
          s <- get
          if name `Set.member` s then
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
        PUnassociated (UParen op) ->
          check op
        PUnassociated (UUnaryOp _ rhs) ->
          check rhs
        PUnassociated (UBinOp _ lhs rhs) ->
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
  -- | Creates an unassociated operator expression
  opUnassociated :: Unassociated Span a -> a
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
  opNamed = TNamed . unmeta
  opUnassociated = TUnassociated
  opApply a b = Right $ TApp a b
  opEffectApply = Just \a b ->
    Right $ TEffApp a b
  opForallEffect = Just TForEff

instance ExprLike (Expr Span) where
  opKind _ = "expression"
  opUnit = EValue VUnit
  opNamed = EGlobal . unmeta
  opUnassociated = EUnassociated
  opApply a b = Right $ EApp a b
  opSeq = Just ESeq

instance ExprLike (Pattern Span) where
  opKind _ = "pattern"
  opUnit = PUnit
  opNamed name = PCons name []
  opUnassociated = PUnassociated
  opApply (PCons name xs :&: _) x =
    Right $ PCons name (xs ++ [x])
  opApply _ x =
    Left $ copyInfo x "pattern arguments can only occur immediately following a named pattern"

