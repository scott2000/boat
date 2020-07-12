-- | Basic definitions that will be used in all other modules
module Utility.Basics
  ( -- * Paths and Names
    Name (..)
  , getNameString
  , parsePackageName
  , parseModuleName
  , pattern Underscore
  , Path (Path, unpath)
  , toPath
  , (.|.)
  , pattern Core
  , pattern Local
  , pattern EmptyPath
  , pattern NoFile

    -- * Global Compiler State
  , CompileOptions (..)
  , CompileState (..)
  , initialCompileState
  , CompileIO (..)
  , MonadCompile (..)
  , liftIO
  , compileOptions
  , compileState
  , compileModify
  , compileModifyIO
  , CompileError (..)
  , compileError
  , Phase (..)
  , ErrorKind (..)
  , SpecialError (..)
  , ErrorCategory (..)
  , AddError
  , addError
  , ErrorCount (..)
  , AnonCount
  , pattern AnonAny
  , getNewAnon

    -- * Positions and Spans
  , Position (..)
  , Span (..)
  , pattern NoSpan
  , pointSpan
  , isSpanValid

    -- * Language Information
  , Prec (..)
  , isKeyword
  , isIdentFirst
  , isIdentRest
  , isOperatorChar
  , indentationIncrement

    -- * Formatting and Capitalization
  , plural
  , ordinal
  , aOrAn
  , isCap
  , capFirst
  , lowerFirst

    -- * General Helper Functions
  , hashMapGet
  , (<&>)
  ) where

import GHC.Generics (Generic)

import Data.Char
import Data.Word
import Data.List

import Data.IORef
import Data.Bits (xor)
import Data.Hashable

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

import Text.Megaparsec (ParsecT, Stream)

-- | An identifier to be used to name items
data Name
  = Identifier String
  | Operator String
  | Unary String
  deriving (Ord, Eq, Generic)

instance Hashable Name

instance Show Name where
  show = \case
    Identifier ident -> ident
    Operator op -> "(" ++ op ++ ")"
    Unary u -> "(unary " ++ u ++ ")"

-- | Gets the string part of a 'Name', ignoring the kind
getNameString :: Name -> String
getNameString = \case
  Identifier ident -> ident
  Operator op -> op
  Unary u -> u

-- | A path consisting of a series of names separated by dots
data Path = Path
  { unpath :: [Name]
  , pathHash :: Int }

-- | Construct a new path, caching the hash value automatically
toPath :: [Name] -> Path
toPath names = Path
  { unpath = names
  , pathHash = hash names }

instance Hashable Path where
  hashWithSalt salt Path { pathHash } =
    -- This is the implementation used by "Hashable"
    (salt * 16777619) `xor` pathHash
  hash Path { pathHash } = pathHash

instance Eq Path where
  Path a ha == Path b hb =
    ha == hb && a == b

instance Ord Path where
  Path a _ `compare` Path b _ =
    a `compare` b

instance Show Path where
  show = intercalate "." . map show . unpath

-- | Add a name to the end of a 'Path'
(.|.) :: Path -> Name -> Path
p .|. name = toPath (unpath p ++ [name])

-- | A helper to make a 'Path' without considering hashing
pattern DefaultPath :: [Name] -> Path
pattern DefaultPath names <- Path { unpath = names }
  where DefaultPath = toPath

-- | Place an item in the Core module
pattern Core :: Name -> Path
pattern Core name = DefaultPath [Identifier "Core", name]

-- | An unqualified local 'Path'
pattern Local :: Name -> Path
pattern Local name = DefaultPath [name]

-- | A name starting with an underscore which will not be exported
pattern Underscore :: String -> Name
pattern Underscore name = Identifier ('_':name)

-- | An empty 'Path'
pattern EmptyPath :: Path
pattern EmptyPath = DefaultPath []

-- | An empty 'FilePath' for missing file information (e.g. for generated code)
pattern NoFile :: FilePath
pattern NoFile = ""

-- | Helper function for 'parsePackageName' and 'parseModuleName'
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
      else if isKeyword name then
        Left (kind ++ " cannot be a keyword")
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
        else if not $ isUpper first then
          Left (kind ++ " must start with an uppercase letter, did you mean `" ++ capFirst name ++ "`?")
        else
          Right $ Identifier name
      else
        Right $ Identifier name
  where
    isAlphaNumAscii x = (x == '_' || isAlpha x || isDigit x) && isAscii x

-- | Parse a package name (used for parsing a command-line argument)
parsePackageName :: String -> Either String Name
parsePackageName = parseIdentIn "package name" True

-- | Parse a module name (used for parsing directory names for modules)
parseModuleName :: String -> Either String Name
parseModuleName = parseIdentIn "module names" False

-- | A unique identifier used for inference
type AnonCount = Word64

-- | Matches any `AnonCount`, defaulting to 0 if used in an expression
pattern AnonAny :: Word64
pattern AnonAny <- _
  where AnonAny = 0

-- | A record of options provided as command-line arguments
data CompileOptions = CompileOptions
  { -- | The requested file or directory to be compiled
    compileTarget :: !FilePath
    -- | The requested name for the package
  , compilePackageName :: !Name
    -- | Whether error explanations are enabled
  , compileExplainErrors :: !Bool }

-- | Represents a monad containing a 'CompileIO', allowing modifications to compile state
class MonadIO m => MonadCompile m where
  -- | Lift a computation from 'CompileIO'
  liftCompile :: CompileIO a -> m a

instance MonadCompile CompileIO where
  liftCompile = id

instance MonadCompile m => MonadCompile (StateT s m) where
  liftCompile = lift . liftCompile

instance MonadCompile m => MonadCompile (ReaderT s m) where
  liftCompile = lift . liftCompile

instance MonadCompile m => MonadCompile (MaybeT m) where
  liftCompile = lift . liftCompile

instance (MonadCompile m, Monoid w) => MonadCompile (WriterT w m) where
  liftCompile = lift . liftCompile

instance (MonadCompile m, Stream s) => MonadCompile (ParsecT e s m) where
  liftCompile = lift . liftCompile

-- | Gets the 'CompileOptions' from 'CompileIO'
compileOptions :: MonadCompile m => m CompileOptions
compileOptions = liftCompile $ CompileIO $ asks fst

-- | Gets the 'CompileState' from 'CompileIO'
compileState :: MonadCompile m => m CompileState
compileState = compileModifyIO readIORef

-- | Modifies the 'CompileState' in 'CompileIO'
compileModify :: MonadCompile m => (CompileState -> CompileState) -> m ()
compileModify f = compileModifyIO \r ->
  modifyIORef' r f

-- | Modifies the 'CompileState' in 'CompileIO' using the 'IORef'
compileModifyIO :: MonadCompile m => (IORef CompileState -> IO a) -> m a
compileModifyIO = liftCompile . CompileIO . ReaderT . (. snd)

-- | 'StateT' used for all stages of compilation to store state
newtype CompileIO a = CompileIO
  { runCompileIO :: ReaderT (CompileOptions, IORef CompileState) IO a }
  deriving (Functor, Applicative, Monad, MonadIO)

-- | A record used to store state throughout compilation
data CompileState = CompileState
  { -- | The current phase of compilation
    compilePhase :: !Phase
    -- | The set of errors emitted during compilation
  , compileErrors :: !(Set CompileError)
    -- | The count of each type of error emitted
  , compileErrorCount :: !ErrorCount
    -- | The last unique 'AnonCount' that was given out
  , compileAnonCount :: !AnonCount }

-- | Creates a 'CompileState' from 'CompileOptions'
initialCompileState :: CompileState
initialCompileState = CompileState
  { compileErrors = Set.empty
  , compilePhase = PhaseInit
  , compileErrorCount = ErrorCount
    { errorCount = 0
    , warningCount = 0
    , hasPrimaryError = False
    , hasExplainError = False }
  , compileAnonCount = AnonAny }

-- | A phase of compilation (see "Parse" and "Analyze")
data Phase
  -- | Any initialization in "Main" that occurs before parsing begins
  = PhaseInit
  -- | The parsing phase defined in "Parse" ('Parse.parse')
  | PhaseParser
  -- | The name resolution phase defined in "Analyze.NameResolve" ('Analyze.NameResolve.nameResolve')
  | PhaseNameResolve
  -- | The operator association phase defined in "Analyze.AssocOps" ('Analyze.AssocOps.assocOps')
  | PhaseAssocOps
  -- | The variance inference phase defined in "Analyze.InferVariance" ('Analyze.InferVariance.inferVariance')
  | PhaseInferVariance
  -- | The type inference phase defined in "Analyze.InferTypes" ('Analyze.InferTypes.inferTypes')
  | PhaseInferTypes

-- | Gets a new unique 'AnonCount' for an inference variable
getNewAnon :: MonadCompile m => m AnonCount
getNewAnon = compileModifyIO \r -> do
  s <- readIORef r
  let newCount = compileAnonCount s + 1
  let s' = s { compileAnonCount = newCount }
  s' `seq` writeIORef r s'
  return newCount

-- | An error encountered during compilation
data CompileError = CompileError
  { -- | The file in which the error occurred (optional)
    errorFile :: !FilePath
    -- | The span at which the error occurred (requires a file)
  , errorSpan :: !Span
    -- | The kind of error that occurred
  , errorKind :: !ErrorKind
    -- | The general category of error (for explanations)
  , errorCategory :: ![ErrorCategory]
    -- | An explanation that is more specific to this error
  , errorExplain :: !(Maybe String)
    -- | The basic error message to print
  , errorMessage :: String }
  deriving Eq

instance Ord CompileError where
  a `compare` b =
    errorFile a `shortLast` errorFile b
    <> errorSpan a `compare` errorSpan b
    <> errorKind a `compare` errorKind b
    <> errorCategory a `compare` errorCategory b
    <> errorExplain a `compare` errorExplain b
    <> errorMessage a `compare` errorMessage b
    where
      -- Short file paths should appear last
      []     `shortLast` []     = EQ
      []     `shortLast` _      = GT
      _      `shortLast` []     = LT
      (a:as) `shortLast` (b:bs) =
        a `compare` b <> as `shortLast` bs

-- | A default 'CompileError' containing everything but a message
compileError :: CompileError
compileError = CompileError
  { errorFile = NoFile
  , errorSpan = NoSpan
  , errorKind = Error
  , errorCategory = []
  , errorExplain = Nothing
  , errorMessage = error "compileError was not given an error message" }

-- | A general category of error that may need an in-depth explanation
data ErrorCategory
  = ECAssocOps
  | ECVariance
  deriving (Ord, Eq)

-- | Stores the number of each type of error (useful for determining when to stop compilation)
data ErrorCount = ErrorCount
  { errorCount :: !Int
  , warningCount :: !Int
  , hasPrimaryError :: !Bool
  , hasExplainError :: !Bool }

instance Show ErrorCount where
  show ErrorCount { errorCount, warningCount }
    | warningCount == 0 = plural errorCount "error"
    | errorCount == 0 = plural warningCount "warning"
    | otherwise = plural errorCount "error" ++ " (and " ++ plural warningCount "warning" ++ ")"

-- | Adds a new error to the 'ErrorCount'
updateErrorCount :: ErrorKind -> ErrorCount -> ErrorCount
updateErrorCount Error c = c
  { errorCount = errorCount c + 1
  , hasPrimaryError = True }
updateErrorCount Warning c = c
  { warningCount = warningCount c + 1 }
updateErrorCount _ c = c

-- | Represents the different kinds of possible error messages
data ErrorKind
  = Info
  | Warning
  | Error
  | Done
  | Explain ErrorKind
  | SpecialError SpecialError
  deriving (Ord, Eq)

instance Show ErrorKind where
  show = \case
    Info      -> "info"
    Warning   -> "warning"
    Error     -> "error"
    Done      -> "done"
    Explain _ -> "explain"
    _         -> "other"

-- | A kind of error that is handled specially when being added
data SpecialError
  = SecondaryError
  deriving (Ord, Eq)

-- | Constraint for a 'Monad' that supports adding errors (e.g. 'CompileIO')
type AddError = MonadCompile

-- | Emits a single 'CompileError' for later printing
addError :: AddError m => CompileError -> m ()
addError err =
  compileModify \s ->
    if err `Set.member` compileErrors s then
      -- Don't try to insert the error if there is already an exact duplicate of the error
      s
    else
      let count = compileErrorCount s in
      case errorKind err of
        SpecialError SecondaryError
          | hasPrimaryError count -> s
          | otherwise ->
            add err { errorKind = Error } count { errorCount = errorCount count + 1 } s
        kind ->
          add err (updateErrorCount kind count) s
  where
    add err count s = s
      { compileErrors = Set.insert err $ compileErrors s
      , compileErrorCount =
        case (errorCategory err, errorExplain err) of
          ([], Nothing) -> count
          _ -> count { hasExplainError = True } }

-- | A position in a file consisting of a line number and column number (starting at 1)
data Position = Position
  { posLine :: !Int
  , posColumn :: !Int }
  deriving (Ord, Eq)

instance Show Position where
  show Position { posLine, posColumn } =
    show posLine ++ ":" ++ show posColumn

-- | A range of text in the interval [spanStart, spanEnd) to be associated with parsed code
data Span = Span
  { spanStart :: !Position
  , spanEnd :: !Position }

-- | Invalid spans are sorted to be after valid spans
instance Ord Span where
  a `compare` b =
    case (isSpanValid a, isSpanValid b) of
      (False, False) -> EQ
      (False, _)     -> GT
      (_,     False) -> LT
      (True,  True)  ->
        spanStart a `compare` spanStart b
        <> spanEnd a `compare` spanEnd b

instance Eq Span where
  NoSpan == NoSpan = True
  Span s0 e0 == Span s1 e1 =
    s0 == s1 && e0 == e1

instance Show Span where
  show NoSpan = "<unknown>"
  show Span { spanStart } =
    show spanStart

-- | Creates a span from the ends of two other spans, preserving 'NoSpan'
instance Semigroup Span where
  Span { spanStart } <> Span { spanEnd } =
    Span { spanStart, spanEnd }

-- | Pattern for a missing span (considered invalid by 'isSpanValid')
pattern NoSpan :: Span
pattern NoSpan <- (isSpanValid -> False)
  where NoSpan = Span (Position 0 0) (Position 0 0)

-- | Creates a 'Span' of a single character from a 'Position'
pointSpan :: Position -> Span
pointSpan pos = Span
  { spanStart = pos
  , spanEnd = pos { posColumn = posColumn pos + 1 } }

-- | Checks if a span consists of only valid positions (@'posLine' > 0@)
isSpanValid :: Span -> Bool
isSpanValid Span { spanStart, spanEnd } =
  isPositionValid spanStart && isPositionValid spanEnd
  where
    isPositionValid Position { posLine } =
      posLine > 0

-- | Represents the precedence of a type of operation
data Prec
  -- | A special precedence for when an expression will be terminated by a special operator
  = ExpectEndPrec
  -- | The default precedence for an expression
  | MinPrec
  -- | The precedence for a special operator like @(->)@
  | SpecialPrec
  -- | The precedence for a regular operator surrounded by whitespace
  | NormalPrec
  -- | The precedence for function application
  | ApplyPrec
  -- | The precedence for a compact operator not surrounded by whitespace
  | CompactPrec
  deriving (Ord, Eq)

-- | A set of strings that are considered keywords
keywords :: HashSet String
keywords = HashSet.fromList
  [ "_"
  , "use"
  , "mod"
  , "operator"
  , "type"
  , "effect"
  , "data"
  , "let"
  , "with"
  , "fun"
  , "match"
  , "unary" ]

-- | Checks if a given string is a keyword
isKeyword :: String -> Bool
isKeyword w = w `HashSet.member` keywords

-- | Checks if a character is valid at the start of an identifier
isIdentFirst :: Char -> Bool
isIdentFirst x = (isAlpha x || x == '_') && isAscii x

-- | Checks if a character is valid after the first character of an identifier
isIdentRest :: Char -> Bool
isIdentRest  x = (isAlpha x || isDigit x || x == '_') && isAscii x

-- | Checks if a character is valid in an infix or unary operator
isOperatorChar :: Char -> Bool
isOperatorChar w = w `elem` ("+-*/%^!=<>:?|&~$." :: String)

-- | The number of spaces to insert for indentation
indentationIncrement :: Int
indentationIncrement = 2

-- | Prepends a number to a string with an optional plural suffix
plural :: Int -> String -> String
plural 0 w = "no " ++ w ++ "s"
plural 1 w = "1 " ++ w
plural n w = show n ++ " " ++ w ++ "s"

-- | Converts a zero-based index to an ordinal number (1st, 2nd, 3rd, 4th, etc.)
ordinal :: Int -> String
ordinal index =
  show num ++ suffix num
  where
    num = index + 1
    suffix 1 = "st"
    suffix 2 = "nd"
    suffix 3 = "rd"
    suffix n
      | n > 20    = suffix (n `rem` 10)
      | otherwise = "th"

-- | Prepends an indefinite article to a string depending on whether it starts with a vowel
aOrAn :: String -> String
aOrAn str = article ++ str
  where
    article =
      if isLowerVowel $ toLower $ head str then
        "an "
      else
        "a "
    isLowerVowel = \case
      'a' -> True
      'e' -> True
      'i' -> True
      'o' -> True
      'u' -> True
      _ -> False

-- | Checks if a character is considered uppercase (A-Z or _)
isCap :: Char -> Bool
isCap ch
  | ch `elem` ['A'..'Z'] || ch == '_' = True
  | otherwise = False

-- | Converts the first character in a string to uppercase
capFirst :: String -> String
capFirst (x:xs) = toUpper x : xs
capFirst _ = error "capFirst called on empty string"

-- | Converts the first character in a string to lowercase
lowerFirst :: String -> String
lowerFirst (x:xs) = toLower x : xs
lowerFirst _ = error "lowerFirst called on empty string"

-- | A version of 'HashMap.lookup' that calls 'error' with the key if it fails
hashMapGet :: (Show k, Eq k, Hashable k) => k -> HashMap k v -> v
hashMapGet key m =
  case HashMap.lookup key m of
    Just v -> v
    Nothing ->
      error ("HashMap does not contain key: " ++ show key)

-- | A flipped version of 'fmap'
(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

