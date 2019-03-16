
module Lib.Vec where

open import Prelude
open import Variables hiding (xs; ys)

private
  variable
    xs ys : Vec A n

infix 3 _∈_
data _∈_ (x : A) : Vec A n → Set where
  zero : x ∈ x ∷ xs
  suc  : x ∈ xs → x ∈ y ∷ xs

_∈?_ : ⦃ _ : Eq A ⦄ (x : A) (xs : Vec A n) → Dec (x ∈ xs)
x ∈? [] = no λ ()
x ∈? (y ∷ xs) with x == y
... | yes refl = yes zero
... | no neq  with x ∈? xs
...   | yes x∈xs = yes (suc x∈xs)
...   | no x∉xs  = no λ where
                      zero       → neq refl
                      (suc x∈xs) → x∉xs x∈xs

deleteIx : (xs : Vec A (suc n)) → x ∈ xs → Vec A n
deleteIx (_ ∷ xs) zero          = xs
deleteIx (x ∷ xs) (suc zero)    = x ∷ deleteIx xs zero
deleteIx (x ∷ xs) (suc (suc i)) = x ∷ deleteIx xs (suc i)
