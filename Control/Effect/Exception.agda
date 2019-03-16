
module Control.Effect.Exception where

open import Prelude
open import Control.Effect
open import Variables

data Exception (Err : Set) : Effect where
  raise : Err → Exception Err A [- ⊤ -]

EXCEPTION : Set → List EFFECT
EXCEPTION Err = [ Exception Err ⊢ ⊤ ]

instance
  HandlerExceptionEither : Handler (Exception A) (Either A)
  HandlerExceptionEither .handle _ (raise err) k = left err
