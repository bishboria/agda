
module Agda.TypeChecking.Reduce.Fast where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

fastReduce :: Term -> ReduceM (Blocked Term)

