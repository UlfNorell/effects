
module Control.Effect.State where

open import Prelude hiding (_>>=_; _>>_; putStr)
open import Container.List
open import Control.Effect renaming (bindEff to _>>=_; thenEff to _>>_)
open import Variables
open import Lib

data State : Effect where
  get : State A [ A => A ]
  put : B → State ⊤ [ A => B ]

instance
  HandleState : Handler State M
  HandleState .handle s get     k = k s s
  HandleState .handle s (put x) k = k _ x

STATE : Set → List EFFECT
STATE S = [ State ⊢ S ]

modify : (A → B) → Eff M A [ STATE A => STATE B ]
modify f = do
  x ← call get
  call (put (f x))
  ret x

runS : Eff id A [ STATE B => STATE C ] → B → A × C
runS m s = runEff (s ∷ []) m λ { x (s′ ∷ []) → x , s′ }
