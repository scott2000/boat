-- | Basic definitions that will be used in all other modules
module Utility.Basics
  ( -- * Paths and Names
    Name (..)
  , getNameString
  , parsePackageName
  , parseModuleName
  , pattern Underscore
  , Path (..)
  , (.|.)
  , pattern Core
  , pattern Local
  , pattern EmptyPath
  , pattern Generated
  , pattern DefaultFile

    -- * Global Compiler State
  , MonadCompile (..)
  , liftIO
  , CompileIO (..)
  , CompileState (..)
  , compileStateFromOptions
  , CompileOptions (..)
  , CompileError (..)
  , compileError
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
  , pointSpan

    -- * Formatting and Capitalization
  , plural
  , ordinal
  , aOrAn
  , isKeyword
  , isCap
  , capFirst
  , lowerFirst

    -- * General Helper Functions
  , mapGet
  , (<&>)
  ) where

import Data.Char
import Data.Word
import Data.List
import Data.String

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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
  deriving (Ord, Eq)

instance IsString Name where
  fromString = Identifier

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

-- | Add a name to the end of a 'Path'
(.|.) :: Path -> Name -> Path
(Path p) .|. name = Path (p ++ [name])

-- | Place an item in the Core module
pattern Core :: Name -> Path
pattern Core name = Path ["Core", name]

-- | Make an unqualified 'Path'
pattern Local :: Name -> Path
pattern Local name = Path [name]

-- | A name starting with an underscore which will not be exported
pattern Underscore :: String -> Name
pattern Underscore name = Identifier ('_':name)

-- | Make an empty 'Path'
pattern EmptyPath :: Path
pattern EmptyPath = Path []

-- | Placeholder filename for compiler-generated code
pattern Generated :: FilePath
pattern Generated = "<compiler-generated>"

-- | Same as 'Generated', but matches any file as a pattern
pattern DefaultFile :: FilePath
pattern DefaultFile <- _
  where DefaultFile = Generated

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

-- | 'StateT' used for all stages of compilation to store state
newtype CompileIO a = CompileIO
  { runCompileIO :: StateT CompileState IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadState CompileState)

-- | A record used to store state throughout compilation
data CompileState = CompileState
  { -- | The options given to the compiler
    compileOptions :: !CompileOptions
    -- | The set of errors emitted during compilation
  , compileErrors :: !(Set CompileError)
    -- | The count of each type of error emitted
  , compileErrorCount :: !ErrorCount
    -- | The last unique 'AnonCount' that was given out
  , compileAnonCount :: !AnonCount }

-- | A record of options provided as command-line arguments
data CompileOptions = CompileOptions
  { -- | The requested file or directory to be compiled
    compileTarget :: !FilePath
    -- | The requested name for the package
  , compilePackageName :: !Name
    -- | Whether error explanations are enabled
  , compileExplainErrors :: !Bool }

-- | Creates a 'CompileState' from 'CompileOptions'
compileStateFromOptions :: CompileOptions -> CompileState
compileStateFromOptions opts = CompileState
  { compileOptions = opts
  , compileErrors = Set.empty
  , compileErrorCount = ErrorCount
    { errorCount = 0
    , warningCount = 0
    , hasPrimaryError = False
    , hasExplainError = False }
  , compileAnonCount = AnonAny }

-- | Gets a new unique 'AnonCount' for an inference variable
getNewAnon :: MonadCompile m => m AnonCount
getNewAnon = liftCompile do
  s <- get
  let newCount = compileAnonCount s + 1
  put s { compileAnonCount = newCount }
  return newCount

-- | An error encountered during compilation
data CompileError = CompileError
  { -- | The file in which the error occurred (optional)
    errorFile :: !(Maybe FilePath)
    -- | The span at which the error occurred (requires a file)
  , errorSpan :: !(Maybe Span)
    -- | The kind of error that occurred
  , errorKind :: !ErrorKind
    -- | The general category of error (for explanations)
  , errorCategory :: !(Maybe ErrorCategory)
    -- | An explanation that is more specific to this error
  , errorExplain :: !(Maybe String)
    -- | The basic error message to print
  , errorMessage :: String }
  deriving Eq

instance Ord CompileError where
  a `compare` b =
    errorFile a `reversedMaybe` errorFile b
    <> errorSpan a `reversedMaybe` errorSpan b
    <> errorKind a `compare` errorKind b
    <> errorCategory a `compare` errorCategory b
    <> errorExplain a `compare` errorExplain b
    <> errorMessage a `compare` errorMessage b
    where
      -- Empty files and spans should appear last
      Nothing `reversedMaybe` Nothing = EQ
      Nothing `reversedMaybe` Just _  = GT
      Just _  `reversedMaybe` Nothing = LT
      Just a  `reversedMaybe` Just b  = a `compare` b

-- | A default 'CompileError' containing everything but a message
compileError :: CompileError
compileError = CompileError
  { errorFile = Nothing
  , errorSpan = Nothing
  , errorKind = Error
  , errorCategory = Nothing
  , errorExplain = Nothing
  , errorMessage = error "compileError was not given an error message" }

-- | A general category of error that may need an in-depth explanation
data ErrorCategory
  = ECAssocOps
  | ECInferVariance
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
  liftCompile $ modify \s ->
    if Set.member err $ compileErrors s then
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
          (Nothing, Nothing) -> count
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
  deriving (Ord, Eq)

instance Show Span where
  show = show . spanStart

instance Semigroup Span where
  Span { spanStart } <> Span { spanEnd } =
    Span { spanStart, spanEnd }

-- | Creates a 'Span' of a single character from a 'Position'
pointSpan :: Position -> Span
pointSpan pos = Span
  { spanStart = pos
  , spanEnd = pos { posColumn = posColumn pos + 1 } }

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

-- | A set of strings that are considered keywords
keywords :: Set String
keywords = Set.fromList
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
isKeyword w = w `Set.member` keywords

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

-- | A version of 'Map.lookup' that calls 'error' with the key if it fails
mapGet :: (Show k, Ord k) => k -> Map k v -> v
mapGet key m =
  case Map.lookup key m of
    Just v -> v
    Nothing ->
      error ("map does not contain key: " ++ show key)

-- | A flipped version of 'fmap'
(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

