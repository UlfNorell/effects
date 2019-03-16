
module Example where

open import Prelude hiding (putStrLn; _>>=_; _>>_)
open import Container.List
open import Control.Effect renaming (bindEff to _>>=_; thenEff to _>>_)
open import Control.Effect.State
open import Control.Effect.Console
open import Control.Effect.File
open import Variables

greeting : Eff M ⊤ [- CONSOLE -]
greeting = do
  call putStrLn "What is your name?"
  name ← call getLine
  call putStrLn ("Hello " & name & ", 会えてうれしいよ")

test-io : Eff M Nat [- STATE Nat ∧ CONSOLE -]
test-io = do
  x ← call get
  call (putStrLn ("x = " & show x))
  ret x

copyLine : (hᵢ : FileHandle readMode) (hₒ : FileHandle writeMode) →
           Eff M ⊤ [- FILE (Open hᵢ) ∧ FILE (Open hₒ) -]
copyLine hᵢ hₒ = do
  s ← call fReadLine hᵢ
  call fWriteLine hₒ s

example : ⦃ _ : Handler FileIO M ⦄ → Eff M ⊤ [- CONSOLE -]
example = do
  call putStrLn "Starting"
  n ← new (STATE Nat) 42 do
        s  ← lift (modify suc)
        s' ← call get
        ret (s * s')
  call putStrLn $ "n = " & show n
  new (FILE Closed) _ (new (FILE Closed) _ do
    success h ← call openFile "in.txt" readMode
      where failure _ → do
              call putStrLn "Failed to open file"
              ret _
    call putStrLn "Opened input file"
    success h₁ ← call openFile "out.txt" writeMode
      where failure _ → call closeFile h
    call putStrLn "Opened output file"
    lift copyLine h h₁
    lift copyLine h h₁
    s ← call fReadLine h
    call putStrLn $ "Third line: " & s
    call closeFile h₁
    call closeFile h)
  ret _

main : IO ⊤
main = runEff (_ ∷ []) greeting λ _ _ → return _
