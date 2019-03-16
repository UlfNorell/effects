
module Control.Effect.Random where

open import Prelude
open import Control.Effect
open import Variables

postulate
  StdGen : Set

private
  postulate
    randomR : Nat → IO Nat

{-# FOREIGN GHC import System.Random #-}
{-# COMPILE GHC randomR = \ n -> randomRIO (0, n) #-}

data Random : Effect where
  randomNat : (n : Nat) → Random (Fin (suc n)) [- ⊤ -]

RND : List EFFECT
RND = [ Random ⊢ ⊤ ]

isTrue? : (b : Bool) → Dec (IsTrue b)
isTrue? false = no λ ()
isTrue? true = yes true

private
  toFin! : Nat → Fin (suc n)
  toFin! {n} m with isTrue? (lessNat m (suc n))
  ... | yes p = natToFin m ⦃ p ⦄
  ... | no _  = zero

instance
  HandleRandom : Handler Random IO
  HandleRandom .handle g (randomNat n) k = do
    x ← randomR n
    k (toFin! x) _
