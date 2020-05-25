-- | Parse all files in a given directory, or parse a single file
module Parse (parse) where

import Utility
import Parse.Module

import System.FilePath
import System.Directory
import System.Exit (exitFailure)

import Data.List (sort)
import Control.Monad.State.Strict

-- | Parse source code from a given path
parse :: CompileIO [Module]
parse = do
  path <- gets (compileTarget . compileOptions)
  isDir <- lift $ doesDirectoryExist path
  if isDir then
    parseDirectory path
  else do
    isFile <- lift $ doesFileExist path
    if isFile then
      case takeExtension path of
        ".boat" ->
          parseSingleFile path <&> prependModule []
        other -> lift do
          let ext = if null other then "no extension" else other
          putStrLn ("Error: expected extension of .boat for file, found " ++ ext)
          exitFailure
    else lift do
      putStrLn ("Error: cannot find file or directory at `" ++ path ++ "`")
      exitFailure

-- | Check if a file has the extension @.boat@
isBoatExtension :: FilePath -> Bool
isBoatExtension = (".boat" ==) . takeExtension

-- | Check if a directory contains files with the correct extension
containsBoatFiles :: FilePath -> IO Bool
containsBoatFiles path = do
  files <- listDirectory path
  checkAll files
  where
    checkAll [] = return False
    checkAll (file:rest) =
      if isBoatExtension file then do
        isFile <- doesFileExist (path </> file)
        if isFile then
          return True
        else
          checkAll rest
      else
        checkAll rest

-- | Prepend a module to a list of modules
prependModule :: [Module] -> Module -> [Module]
prependModule mods mod
  | modIsEmpty mod = mods
  | otherwise      = mod : mods

-- | Parse everything in a given path
parseAll :: FilePath -> CompileIO Module
parseAll path = do
  isDir <- lift $ doesDirectoryExist path
  if isDir then
    case parseModuleName $ takeFileName path of
      Right name ->
        moduleFromSubs name <$> parseDirectory path
      Left err -> do
        shouldWarn <- lift $ containsBoatFiles path
        when shouldWarn $
          addError CompileError
            { errorFile = Just path
            , errorSpan = Nothing
            , errorKind = Warning
            , errorMessage =
              "folder contains .boat files but doesn't have a valid module name"
              ++ "\n(" ++ err ++ ")" }
        return defaultModule
  else if isBoatExtension path then
    parseSingleFile path
  else
    return defaultModule

-- | Parse everything in a given directory
parseDirectory :: FilePath -> CompileIO [Module]
parseDirectory path = do
  files <- lift $ sort <$> listDirectory path
  forEach files []
  where
    forEach []          mods = return mods
    forEach (file:rest) mods =
      parseAll (path </> file) >>= forEach rest . prependModule mods

