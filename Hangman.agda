
module Hangman where

open import Prelude
-- open import Container.List
open import Control.Effect
open import Variables
open import Lib
open import Lib.Vec

private
  variable g l : Nat

data GameState : Set where
  running : (g l : Nat) → GameState
  notRunning : GameState

private
  variable s : GameState

initialGuesses : Nat
initialGuesses = 6

letters : String → List Char
letters s = uniq (unpackString s)

blankWord : String → Vec Char n → String
blankWord s missing = mconcat $ map blank $ unpackString s
  where
    blank : Char → String
    blank c with c ∈? missing
    ... | yes _ = "_"
    ... | no  _ = packString [ c ]

data Mystery : GameState → Set where
  initSt   : Mystery notRunning
  gameWon  : (w : String) → Mystery notRunning
  gameLost : (w : String) → Mystery notRunning
  running  : (w : String) (got : List Char) (missing : Vec Char l) →
             Mystery (running g l)

instance
  showMystery : Show (Mystery s)
  showMystery .showsPrec _ initSt = showString "Game not started"
  showMystery .showsPrec _ (gameWon w) = showString "You won! The word was " ∘ shows w
  showMystery .showsPrec _ (gameLost w) = showString "You lost. The word was " ∘ shows w
  showMystery .showsPrec _ (running {g = g} w got missing) =
    showString (blankWord w missing) ∘ showString "\n" ∘
    shows g ∘ showString " guesses remaining."

data MysteryRules : Effect where
  makeGuess : (c : Char) → MysteryRules Bool
                           [ Mystery (running (suc g) (suc l)) => correct ∙
                             Mystery (if correct then running (suc g) l
                                                 else running g (suc l)) ]
  won  : MysteryRules ⊤ [ Mystery (running g 0) => Mystery notRunning ]
  lost : MysteryRules ⊤ [ Mystery (running 0 l) => Mystery notRunning ]
  newGame : (w : String) →
            MysteryRules ⊤ [ Mystery notRunning =>
                             Mystery (running initialGuesses (length (letters w))) ]
  showState : MysteryRules String [- Mystery s -]

MYSTERY : GameState → List EFFECT
MYSTERY s = [ MysteryRules ⊢ Mystery s ]

instance
  HandleGame : Handler MysteryRules M
  HandleGame .handle (running w got missing) won  k = k _ (gameWon w)
  HandleGame .handle (running w got missing) lost k = k _ (gameLost w)
  HandleGame .handle r (newGame w) k = k _ (running w [] (listToVec (letters w)))
  HandleGame .handle r showState k = k (show r) r
  HandleGame .handle (running w got missing) (makeGuess c) k =
    case c ∈? missing of λ where
      (yes i) → k true (running w (c ∷ got) (deleteIx missing i))
      (no _)  → k false (running w got missing)
