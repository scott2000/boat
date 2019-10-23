module Basics where

import Data.Char
import Data.Word
import Data.List
import Data.String

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict

import System.Console.ANSI.Types (Color (..))

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

pattern Core :: Name -> Path
pattern Core name = Path ["Core", name]

pattern Local :: Name -> Path
pattern Local name = Path [name]

pattern EmptyPath :: Path
pattern EmptyPath = Path []

pattern Generated :: FilePath
pattern Generated = "<compiler-generated>"

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

errorColor :: ErrorKind -> Color
errorColor = \case
  Info    -> Blue
  Warning -> Yellow
  Error   -> Red
  Done    -> Green

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

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

isCap :: Char -> Bool
isCap ch
  | ch `elem` ['A'..'Z'] || ch == '_' = True
  | otherwise = False

capFirst :: String -> String
capFirst (x:xs) = toUpper x : xs

lowerFirst :: String -> String
lowerFirst (x:xs) = toLower x : xs
