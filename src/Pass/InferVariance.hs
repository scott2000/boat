module Pass.InferVariance (inferVariance) where

import Utility.Basics
import Utility.ErrorPrint
import Utility.AST
import Utility.Program

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.State.Strict

data VarianceConstraint = VarianceConstraint
  { vBase :: TypeVariance
  , vDeps :: [AnonCount] }

defaultConstraint :: VarianceConstraint
defaultConstraint = VarianceConstraint
  { vBase = VOutput
  , vDeps = [] }

addStep :: TypeVariance -> VarianceConstraint -> VarianceConstraint
addStep (VAnon anon) cs =
  cs { vDeps = anon : vDeps cs }
addStep other cs =
  cs { vBase = other <> vBase cs }

type DeclMap = Map (Meta Path) (InFile DataDecl)

data InferState = InferState
  { iResolvedDecls :: !DeclMap }

type Infer = StateT InferState CompileIO

lookupDecl :: Meta Path -> Infer (InFile DataDecl)
lookupDecl path = do
  resolvedDecls <- gets iResolvedDecls
  case Map.lookup path resolvedDecls of
    Nothing -> lift $ compilerBug $ "lookupDecl couldn't find `" ++ show path ++ "`"
    Just decl -> return decl

inferVariance :: AllDecls -> CompileIO AllDecls
inferVariance decls = return decls

