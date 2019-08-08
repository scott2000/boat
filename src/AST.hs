module AST where

import Data.Char
import Data.Word
import Data.List
import Data.String
import Data.Semigroup
import Data.Bifunctor

import Data.Map (Map)
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.Reader
import Control.Monad.State.Strict

type CompileIO = StateT CompileState IO

data CompileOptions = CompileOptions
  { compileTarget :: !FilePath
  , compilePackageName :: !Name }
  deriving Show

parseIdentIn :: String -> Bool -> String -> Either String Name
parseIdentIn kind requireUpper name =
  case name of
    [] ->
      Left (kind ++ " cannot be empty")
    (first:rest) ->
      if not $ all isAlphaNumAscii name then
        Left (kind ++ " can only contain alphanumeric ascii characters and underscores")
      else if isDigit first then
        Left (kind ++ " cannot start with a number")
      else if requireUpper then
        if first == '_' then
          let
            suggestion =
              case rest of
                (x:_) | isAlpha x ->
                  ", did you mean `" ++ capFirst rest ++ "`?"
                _ -> ""
          in
            Left (kind ++ " cannot start with an underscore" ++ suggestion)
        else if requireUpper && not (isUpper first) then
          Left (kind ++ " must start with an uppercase letter, did you mean `" ++ capFirst name ++ "`?")
        else
          Right $ Identifier name
      else
        Right $ Identifier name
  where
    isAlphaNumAscii x = (x == '_' || isAlpha x || isDigit x) && isAscii x

parsePackageName :: String -> Either String Name
parsePackageName = parseIdentIn "package name" True

parseModuleName :: String -> Either String Name
parseModuleName = parseIdentIn "module names" False

type AnonCount = Word64

data CompileState = CompileState
  { compileOptions :: !CompileOptions
  , compileErrors :: !(Set CompileError)
  , compileErrorCount :: !ErrorCount
  , compileAnonTypes :: !AnonCount }

compileStateFromOptions :: CompileOptions -> CompileState
compileStateFromOptions opts = CompileState
  { compileOptions = opts
  , compileErrors = Set.empty
  , compileErrorCount = ErrorCount 0 0
  , compileAnonTypes = 0 }

getNewAnon :: MonadState CompileState m => m AnonCount
getNewAnon = do
  s <- get
  let oldCount = compileAnonTypes s
  put s { compileAnonTypes = oldCount + 1 }
  return oldCount

data CompileError = CompileError
  { errorFile :: Maybe FilePath
  , errorSpan :: Maybe Span
  , errorKind :: ErrorKind
  , errorMessage :: String }
  deriving Eq

instance Ord CompileError where
  a `compare` b =
    errorFile a `reversedMaybe` errorFile b
    <> errorSpan a `reversedMaybe` errorSpan b
    <> errorKind a `compare` errorKind b
    <> errorMessage a `compare` errorMessage b
    where
      Nothing `reversedMaybe` Nothing = EQ
      Nothing `reversedMaybe` Just _  = GT
      Just _  `reversedMaybe` Nothing = LT
      Just a  `reversedMaybe` Just b  = a `compare` b

data ErrorCount = ErrorCount
  { errorCount :: !Int
  , warningCount :: !Int }

instance Show ErrorCount where
  show = \case
    ErrorCount e 0 -> plural e "error"
    ErrorCount 0 w -> plural w "warning"
    ErrorCount e w ->
      plural e "error" ++ " (and " ++ plural w "warning" ++ ")"

plural :: Int -> String -> String
plural 0 w = "no " ++ w ++ "s"
plural 1 w = "1 " ++ w
plural n w = show n ++ " " ++ w ++ "s"

updateErrorCount :: ErrorKind -> ErrorCount -> ErrorCount
updateErrorCount Error c = c
  { errorCount = errorCount c + 1 }
updateErrorCount Warning c = c
  { warningCount = warningCount c + 1 }
updateErrorCount _ c = c

data ErrorKind
  = Info
  | Warning
  | Error
  | Done
  deriving (Ord, Eq)

instance Show ErrorKind where
  show = \case
    Info    -> "info"
    Warning -> "warning"
    Error   -> "error"
    Done    -> "done"

addError :: MonadState CompileState m => CompileError -> m ()
addError err =
  modify $ \s -> s
    { compileErrors = Set.insert err $ compileErrors s
    , compileErrorCount =
      updateErrorCount (errorKind err) $ compileErrorCount s }

data Position = Position
  { posLine :: !Int
  , posColumn :: !Int }
  deriving (Ord, Eq)

instance Show Position where
  show Position { posLine, posColumn } =
    show posLine ++ ":" ++ show posColumn

-- location is the interval [spanStart, spanEnd)
data Span = Span
  { spanStart :: !Position
  , spanEnd :: !Position }
  deriving (Ord, Eq)

instance Show Span where
  show = show . spanStart

instance Semigroup Span where
  Span { spanStart } <> Span { spanEnd } =
    Span { spanStart, spanEnd }

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
  show = show . unmeta

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

data InFile a = (:/:)
  { getFile :: FilePath
  , unfile :: a }
  deriving (Functor, Foldable, Traversable)

instance Ord a => Ord (InFile a) where
  (_ :/: a) `compare` (_ :/: b) =
    a `compare` b

instance Eq a => Eq (InFile a) where
  (_ :/: a) == (_ :/: b) = a == b

instance Show a => Show (InFile a) where
  show (_ :/: x) = show x

data AllDecls = AllDecls
  { allDatas :: !(Map (Meta Path) (InFile DataDecl))
  , allLets :: !(Map (Meta Path) (InFile LetDecl)) }

instance Show AllDecls where
  show AllDecls { allDatas, allLets } =
    intercalate "\n"
      [ "datas: " ++ intercalate ", " (map show $ Map.keys allDatas)
      , "lets: " ++ intercalate ", " (map show $ Map.keys allLets) ]

emptyDecls :: AllDecls
emptyDecls = AllDecls
  { allDatas = Map.empty
  , allLets = Map.empty }

-- TODO: consider removing strictness annotation?

data Module = Module
  { modUses :: ![InFile (Meta UseModule)]
  , modSubs :: !(Map Name [Module])
  , modDatas :: !(Map (Meta Name) (InFile DataDecl))
  , modLets :: !(Map (Meta Name) (InFile LetDecl)) }

instance Show Module where
  show mod = intercalate "\n" $ concat
      [ map showUse $ reverse $ modUses mod
      , map showMod $ Map.toList $ modSubs mod
      , map showData $ Map.toList $ modDatas mod
      , map showLet $ Map.toList $ modLets mod ]
    where
      showUse use =
        "use " ++ show use
      showMod (name, mods) =
        intercalate "\n" $ mods <&> \mod ->
          "mod " ++ show name ++ indent (show mod)
      showLet (name, _ :/: LetDecl { letBody }) =
        "let " ++ show name ++ " =" ++ indent (show letBody)
      showData (name, _ :/: DataDecl { dataArgs, dataVariants }) =
        "data " ++ unwords (show name : map unmeta dataArgs)
        ++ " =" ++ indent (intercalate "\n" (map (showVariant . unmeta) dataVariants))
      showVariant (name, types) =
        show name ++ " " ++ unwords (map show types)

defaultModule :: Module
defaultModule = Module
  { modUses = []
  , modSubs = Map.empty
  , modDatas = Map.empty
  , modLets = Map.empty }

moduleFromSubs :: Name -> [Module] -> Module
moduleFromSubs name mods = defaultModule
  { modSubs = Map.singleton name mods }

modIsEmpty :: Module -> Bool
modIsEmpty m =
  null (modUses m)
  && Map.null (modSubs m)
  && Map.null (modDatas m)
  && Map.null (modLets m)

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

modAddUse :: Meta UseModule -> FilePath -> Module -> Module
modAddUse use path mod = mod
  { modUses = path :/: use : modUses mod }

modAddSub :: Name -> Module -> Module -> Module
modAddSub name sub mod =
  if modIsEmpty sub then mod else mod
    { modSubs = Map.insertWith (flip (++)) name [sub] $ modSubs mod }

newtype LetDecl = LetDecl
  { letBody :: Meta Expr }

modAddLet
  :: MonadState CompileState m
  => Meta Name
  -> Meta Expr
  -> FilePath
  -> Module
  -> m Module
modAddLet name body path mod = do
  let
    oldLets = modLets mod
    newDecl = path :/: LetDecl
      { letBody = body }
  when (Map.member name oldLets) $
    addError CompileError
      { errorFile = Just path
      , errorSpan = metaSpan name
      , errorKind = Error
      , errorMessage = "duplicate let binding for name `" ++ show name ++ "`" }
  return mod { modLets = Map.insert name newDecl oldLets }

type DataVariant = (Meta Name, [Meta Type])

data DataDecl = DataDecl
  { dataArgs :: [Meta String]
  , dataVariants :: [Meta DataVariant] }

modAddData
  :: MonadState CompileState m
  => Meta Name
  -> [Meta String]
  -> [Meta DataVariant]
  -> FilePath
  -> Module
  -> m Module
modAddData name args vars path mod = do
  let
    oldDatas = modDatas mod
    newDecl = path :/: DataDecl
      { dataArgs = args
      , dataVariants = vars }
  when (unmeta name /= Operator "->") $
    case find ((Operator "->" ==) . unmeta) $ map (fst . unmeta) vars of
      Just Meta { metaSpan = arrowSpan } ->
        addError CompileError
          { errorFile = Just path
          , errorSpan = arrowSpan
          , errorKind = Warning
          , errorMessage = "data type `" ++ show name ++ "` contains type constructor named (->)" }
      Nothing ->
        return ()
  when (Map.member name oldDatas) $
    addError CompileError
      { errorFile = Just path
      , errorSpan = metaSpan name
      , errorKind = Error
      , errorMessage = "duplicate data type declaration for name `" ++ show name ++ "`" }
  return mod { modDatas = Map.insert name newDecl oldDatas }

variantFromType :: Meta Type -> Either String (Meta DataVariant)
variantFromType typeWithMeta = do
  (f, xs) <- reduceApply typeWithMeta
  case unmeta f of
    TNamed (Path path) ->
      case path of
        [name] ->
          Right $ copySpan typeWithMeta (copySpan f name, xs)
        _ ->
          Left ("data type variant names must be unqualified, did you mean `" ++ show (last path) ++ "`?")
    TPoly local ->
      Left ("data type variant names must be capitalized, did you mean `" ++ capFirst local ++ "`?")
    other ->
      Left ("expected a name for the data type variant, found " ++ show other ++ " instead")

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

-- TODO: visitPath, visitType, visitAll?

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

newtype Path = Path
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

(.|.) :: Path -> Name -> Path
(Path p) .|. name = Path (p ++ [name])

data Type
  = TNamed Path
  | TPoly String
  | TAnon Word64
  | TParen (Meta Type)
  | TUnaryOp (Meta Path) (Meta Type)
  | TBinOp (Meta Path) (Meta Type) (Meta Type)
  | TApp (Meta Type) (Meta Type)
  deriving Eq

instance ExprLike Type where
  opKind _ = "type"
  opUnit = TNamed $ Core $ Identifier "Unit"
  opNamed = TNamed . unmeta
  opParen = TParen
  opUnary = TUnaryOp
  opBinary = TBinOp
  opApply a b = Right $ TApp a b

instance Show Type where
  show = \case
    TNamed path -> show path
    TPoly name -> name
    TAnon _ -> "_"
    TParen ty -> show ty
    TUnaryOp Meta { unmeta = Path [Unary op] } ty ->
      "(" ++ op ++ show ty ++ ")"
    TUnaryOp op ty ->
      "(" ++ show op ++ " " ++ show ty ++ ")"
    TBinOp Meta { unmeta = Path [Operator op] } lhs rhs ->
      "(" ++ show lhs ++ " " ++ op ++ " " ++ show rhs ++ ")"
    TBinOp op lhs rhs ->
      "(" ++ show op ++ " " ++ show lhs ++ " " ++ show rhs ++ ")"
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

pattern Core :: Name -> Path
pattern Core name = Path ["Core", name]

pattern Local :: Name -> Path
pattern Local name = Path [name]

pattern EmptyPath :: Path
pattern EmptyPath = Path []

pattern DefaultMeta :: a -> Meta a
pattern DefaultMeta x <- Meta { unmeta = x }
  where DefaultMeta = meta

pattern Generated :: FilePath
pattern Generated = "<compiler-generated>"

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

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

isCap :: Char -> Bool
isCap ch
  | ch `elem` ['A'..'Z'] || ch == '_' = True
  | otherwise = False

capFirst :: String -> String
capFirst (x:xs) = toUpper x : xs
