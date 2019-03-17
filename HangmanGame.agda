
module HangmanGame where

open import Prelude hiding (putStrLn; _>>=_; _>>_)
open import Control.Effect.State
open import Control.Effect.Console
open import Control.Effect.Random
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

words : Vec String _
words =
  "some" ∷ "random" ∷ "words" ∷ "that" ∷ "are" ∷ "hard" ∷ "to" ∷ "guess" ∷ []

runGame : Eff M ⊤ [- RND ∧ CONSOLE -]
runGame = do
  i ← call randomNat _
  new (MYSTERY notRunning) initSt do
    call newGame (strToUpper $ indexVec words i)
    lift game
    s ← call showState
    call putStrLn s

main : IO ⊤
main = run (_ ∷ _ ∷ []) runGame
