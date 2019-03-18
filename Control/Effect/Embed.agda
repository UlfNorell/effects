
module Control.Effect.Embed where

open import Prelude
open import Control.Effect
open import Variables

-- Embedding an arbitrary monad as an effect

data Embed (M : Set → Set) : Effect where
  lift : M A → Embed M A ⊤ λ _ → ⊤
