
module HangmanGame where

open import Prelude hiding (putStrLn; _>>=_; _>>_; return)
open import Control.Effect.State
open import Control.Effect.Console
open import Control.Effect.Random
open import Control.Effect.File
open import Hangman
open import Variables

private
  variable
    g l : Nat

strToUpper : String → String
strToUpper = packString ∘ map toUpper ∘ unpackString

charGuess : String → Char
charGuess s =
  case unpackString s of λ where
    (c ∷ _) → toUpper c
    []      → '_'

game : Eff M ⊤ [ MYSTERY (running g l) ∧ CONSOLE =>
                 MYSTERY notRunning    ∧ CONSOLE ]
game {l = zero}  = call won
game {g = zero}  = call lost
game {g = suc g} {l = suc l} = do
  s ← call showState
  call putStrLn s
  call putStrLn "Guess a letter!"
  guess ← call getLine
  true ← call makeGuess (charGuess guess)
    where false → do
            call putStrLn "No, sorry"
            game
  call putStrLn "Correct!"
  game

readLines : (n : Nat) (h : FileHandle readMode) → Eff M (Vec String n) [- FILE (Open h) -]
readLines zero h = return []
readLines (suc n) h = do
  s ← call fReadLine h
  ss ← readLines n h
  return (s ∷ ss)

readLinesFrom : ⦃ _ : Handler FileIO M ⦄ → String → (n : Nat) →
                Eff M (Maybe (Vec String n))
                      [- [] -]
readLinesFrom file n = newE (FILE Closed) _ do
  success h ← call openFile file readMode
    where failure _ → return nothing
  xs ← readLines n h
  call closeFile h
  return (just xs)

runGame : ⦃ _ : Handler FileIO M ⦄ → Eff M ⊤ [- RND ∧ CONSOLE -]
runGame = do
  just words ← lift readLinesFrom "words.txt" 200
    where nothing → return _
  i ← call randomNat _
  new (MYSTERY notRunning) initSt do
    call newGame (strToUpper $ indexVec words i)
    lift game
    s ← call showState
    call putStrLn s

main : IO ⊤
main = runE runGame
