
module Variables where

open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Nat

variable
  ℓ ℓ₁ ℓ₂ : Level
  A B C D A′ B′ A₁ B₁ A₂ B₂ : Set ℓ
  xs ys : List A
  x y : A
  F M : Set ℓ → Set ℓ
  n m : Nat
