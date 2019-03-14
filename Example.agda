
module Example where

open import Prelude hiding (putStr; _>>=_; _>>_)
open import Control.Effect renaming (bindEff to _>>=_; thenEff to _>>_)
open import Control.Effect.State
open import Control.Effect.Console
open import Control.Effect.File
open import Variables

test-io : Eff M [ STATE Nat ∷ CONSOLE ∷ [] => STATE Nat ∷ CONSOLE ∷ [] ] Nat
test-io = do
  x ← call get
  call (putStr ("x = " & show x & "\n"))
  ret x

nested : Eff IO [ CONSOLE ∷ FILE ⊤ ∷ [] => CONSOLE ∷ FILE ⊤ ∷ [] ] ⊤
nested = do
  call putStr "Starting\n"
  n ← newE (STATE Nat) 42 do
        s  ← lift (modify suc)
        s' ← call get
        ret (s * s')
  call putStr $ "n = " & show n & "\n"
  newE (FILE ⊤) _ do
    success h ← call openFile "Example.agda" readMode
      where failure _ → do
              call putStr "Failed to open file"
              ret _
    success h₁ ← call openFile "Variables.agda" readMode
      where failure _ → call closeFile h
    call getLine h₁
    s ← call getLine h₁
    call putStr $ "Second line: " & s & "\n"
    call closeFile h
    call closeFile h₁
  ret _

main : IO ⊤
main = runEff (_ ∷ _ ∷ []) nested λ _ _ → return _
