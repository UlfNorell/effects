
module Talk where

open import Prelude hiding (_>>=_; _>>_; putStrLn; return)
open import Control.Monad.Identity
open import Variables

--- ===

{-

  Algebraic Effects in Agda

        Ulf Norell

       Agda Meeting
    Tokyo, Mar 18 2019

 -}





















--- ===

{-

  Algebraic Effects in Agda

            or

   Stealing Stuff from Idris

        Ulf Norell

       Agda Meeting
    Tokyo, Mar 18 2019

 -}


















--- ===

-- Static effects

open import Control.Effect.Console

greeting : Eff M ⊤ [- CONSOLE -]
greeting = do
  call putStrLn "What is your name?"
  name ← call getLine
  call putStrLn $ "Hello " & name & "!"

-- main : IO ⊤
-- main = runE greeting










--- ===

-- Dynamic effects

open import Control.Effect.State

push : A → Eff M ⊤ [ STATE (Vec A n) => STATE (Vec A (suc n)) ]
push x = do
  xs ← call get
  call put (x ∷ xs)

pop : Eff M A [ STATE (Vec A (suc n)) => STATE (Vec A n) ]
pop = do
  x ∷ xs ← call get
  call put xs
  return x

data Exp : Set where
  lit : Nat → Exp
  _⊕_ : Exp → Exp → Exp

exec : Exp → Eff M ⊤ [ STATE (Vec Nat n) => STATE (Vec Nat (suc n)) ]
exec (lit x) = push x
exec (e ⊕ e₁) = do
  exec e
  exec e₁
  a ← pop
  b ← pop
  push (a + b)

execTop : Exp → Eff M Nat [- [] -]
execTop e =
  new (STATE (Vec Nat 0)) [] do
    exec e
    x ∷ [] ← call get
    call put []
    return x

test-exp : Exp
test-exp = (lit 4 ⊕ lit 1) ⊕ lit 6

evalExp : Exp → Nat
evalExp e = runIdentity $ runE (execTop e)







--- ===

-- Dependent effects

getLines : (n : Nat) → Eff M (Vec String n) [- CONSOLE -]
getLines zero = return []
getLines (suc n) = do
  s ← call getLine
  ss ← getLines n
  return (s ∷ ss)

getNat : Eff M Nat [- CONSOLE -]
getNat = do
  s ← call getLine
  case parseNat s of λ where
    (just n) → return n
    nothing  → return 0

read-n-things : Eff M Nat [ CONSOLE ∧ STATE ⊤ => n ∙ CONSOLE ∧ STATE (Vec String n) ]
read-n-things = do
  call putStrLn "How many things do you want?"
  n  ← lift getNat
  call putStrLn "Which ones are they?"
  ss ← lift getLines n
  call put ss
  return n

purge : Eff M ⊤ [ STATE A => STATE ⊤ ]
purge = call put _

-- main : IO ⊤
-- main = runE do
--   n  ← read-n-things
--   xs ← call get
--   call putStrLn ("You want these " & show n & " things: " & show xs)
--   lift purge












--- ===

--- More effects

open import Control.Effect.File

fopen : String → (mode : IOMode) →
        Eff M (FileIOResult (FileHandle mode))
              [ FILE Closed => r ∙ FILE (openFileResource mode r) ]
fopen file mode = call openFile file mode

fclose : ∀ {mode} (h : FileHandle mode) → Eff M ⊤ [ FILE (Open h) => FILE Closed ]
fclose h = call (closeFile h)
