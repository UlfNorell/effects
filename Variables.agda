
module Variables where

open import Agda.Primitive
open import Agda.Builtin.List

variable
  ℓ ℓ₁ ℓ₂ : Level
  A B C : Set ℓ
  xs ys : List A
  x y : A
  F M : Set ℓ → Set ℓ
