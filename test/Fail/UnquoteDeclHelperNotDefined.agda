
module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.TC

infixr 4 _>>=_
_>>=_ = bindTC

pattern `Nat = def (quote Nat) []

unquoteDecl f =
  declareDef (vArg f) `Nat >>= λ _ →
  freshName "aux" >>= λ aux →
  declareDef (vArg aux) `Nat >>= λ _ →
  defineFun f (clause [] (def aux []) ∷ [])