
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

test-state : Eff M [ STATE ⊤ ∷ [] => STATE Nat ∷ [] ] Nat
test-state = do
  call (put 5)
  x ← call get
  ret x

runS : Eff id [ STATE B ∷ [] => STATE C ∷ [] ] A → B → A × C
runS m s = runEff (s ∷ []) m λ { x (s′ ∷ []) → x , s′ }

data ConsoleIO : Effect where
  putStr : String → ConsoleIO ⊤ ⊤ (λ _ → ⊤)

CONSOLE : EFFECT
CONSOLE = mkEff ⊤ ConsoleIO

instance
  HandleConsole : Handler ConsoleIO IO
  HandleConsole .handle _ (putStr s) = λ k → Prelude.putStr s Prelude.>> k _ _

test-io : Eff M [ STATE Nat ∷ CONSOLE ∷ [] => STATE Nat ∷ CONSOLE ∷ [] ] Nat
test-io = do
  x ← call get
  call (putStr ("x = " & show x & "\n"))
  ret x

nested : Eff M [ CONSOLE ∷ [] => CONSOLE ∷ [] ] ⊤
nested = do
  call (putStr "Starting\n")
  n ← newE (STATE Nat) 42 do
        s  ← lift (modify suc)
        s' ← call get
        ret (s * s')
  call (putStr ("n = " & show n & "\n"))
  ret _

main : IO ⊤
main = runEff {M = IO} (_ ∷ []) nested λ _ _ → return _
