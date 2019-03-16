
module Control.Effect.Console where

open import Prelude hiding (putStrLn)
open import Container.List
open import Control.Effect
open import Variables
open import Lib

data ConsoleIO : Effect where
  putStrLn : String → ConsoleIO ⊤ [- ⊤ -]
  getLine  : ConsoleIO String [- ⊤ -]

CONSOLE : List EFFECT
CONSOLE = [ ConsoleIO ⊢ ⊤ ]

private
  postulate
    hsGetLine : IO String

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC hsGetLine = Text.getLine #-}

instance
  HandleConsole : Handler ConsoleIO IO
  HandleConsole .handle _ (putStrLn s) k = do
    Prelude.putStrLn s
    k _ _
  HandleConsole .handle _ getLine k = do
    s ← hsGetLine
    k s _
