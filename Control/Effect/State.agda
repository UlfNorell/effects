
module Control.Effect.State where

open import Prelude hiding (_>>=_; _>>_; putStr)
open import Container.List
open import Control.Effect renaming (bindEff to _>>=_; thenEff to _>>_)
open import Variables
open import Lib

data State : Effect where
  get : State A A (λ _ → A)
  put : B → State ⊤ A (λ _ → B)

instance
  HandleState : Handler State M
  HandleState .handle s get     k = k s s
  HandleState .handle s (put x) k = k _ x

STATE : Set → EFFECT
STATE S = mkEff S State

modify : (A → B) → Eff M [ STATE A ∷ [] => STATE B ∷ [] ] A
modify f = do
  x ← call get
  call (put (f x))
  ret x

runS : Eff id [ STATE B ∷ [] => STATE C ∷ [] ] A → B → A × C
runS m s = runEff (s ∷ []) m λ { x (s′ ∷ []) → x , s′ }
