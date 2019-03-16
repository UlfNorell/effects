
module Example where

open import Prelude hiding (putStr; _>>=_; _>>_)
open import Container.List
open import Control.Effect renaming (bindEff to _>>=_; thenEff to _>>_)
open import Control.Effect.State
open import Control.Effect.Console
open import Control.Effect.File
open import Variables

test-io : Eff M Nat [ STATE Nat ∧ CONSOLE => STATE Nat ∧ CONSOLE ]
test-io = do
  x ← call get
  call (putStr ("x = " & show x & "\n"))
  ret x

copyLine : (hᵢ : FileHandle readMode) (hₒ : FileHandle writeMode) →
           Eff M ⊤ [- FILE (Open hᵢ) ∧ FILE (Open hₒ) -]
copyLine hᵢ hₒ = do
  s ← call fReadLine hᵢ
  call fWrite hₒ (s & "\n")

example : ⦃ _ : Handler FileIO M ⦄ → Eff M ⊤ [- CONSOLE -]
example = do
  call putStr "Starting\n"
  n ← newE (STATE Nat) 42 do
        s  ← lift (modify suc)
        s' ← call get
        ret (s * s')
  call putStr $ "n = " & show n & "\n"
  newE (FILE Closed) _ (newE (FILE Closed) _ do
    success h ← call openFile "in.txt" readMode
      where failure _ → do
              call putStr "Failed to open file\n"
              ret _
    call putStr "Opened input file\n"
    success h₁ ← call openFile "out.txt" writeMode
      where failure _ → call closeFile h
    call putStr "Opened output file\n"
    lift copyLine h h₁
    lift copyLine h h₁
    s ← call fReadLine h
    call putStr $ "Third line: " & s & "\n"
    call closeFile h₁
    call closeFile h)
  ret _

main : IO ⊤
main = runEff (_ ∷ []) example λ _ _ → return _
