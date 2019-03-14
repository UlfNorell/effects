
module Control.Effect.Console where

open import Prelude hiding (_>>=_; _>>_; putStr)
open import Container.List
open import Control.Effect renaming (bindEff to _>>=_; thenEff to _>>_)
open import Variables
open import Lib

data ConsoleIO : Effect where
  putStr : String → ConsoleIO ⊤ ⊤ (λ _ → ⊤)

CONSOLE : EFFECT
CONSOLE = mkEff ⊤ ConsoleIO

instance
  HandleConsole : Handler ConsoleIO IO
  HandleConsole .handle _ (putStr s) = λ k → Prelude.putStr s Prelude.>> k _ _
