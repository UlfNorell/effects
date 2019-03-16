
module Lib where

open import Prelude
open import Container.List
open import Container.Traversable
open import Tactic.Reflection
open import Variables

infix 3 _⊆_
_⊆_ : {A : Set ℓ} → List A → List A → Set ℓ
xs ⊆ ys = All (_∈ ys) xs

private
  vars : Nat → List Term
  vars 0       = []
  vars (suc n) = var n [] ∷ vars n

assumption : Tactic
assumption ?hole = do
  cxt ← getContext
  choice (map (unify ?hole) (vars (length cxt)))

pattern _`∷_ x xs = con (quote List._∷_) (_ ∷ _ ∷ vArg x ∷ vArg xs ∷ [])

private
  indices′ : Term → Term → List Term
  indices′ (_ `∷ xs) t =
    t ∷ indices′ xs (con₁ (quote Any.suc) t)
  indices′ _    _ = []

  indices : Term → List Term
  indices xs = indices′ xs (con₁ (quote Any.zero) (con₀ (quote refl)))

nometaSpine : Term → TC ⊤
nometaSpine (_ `∷ xs) = nometaSpine xs
nometaSpine (con _ _) = return _
nometaSpine (var _ _) = return _
nometaSpine x = ensureNoMetas x

tac-find-index' : Tactic → Tactic
tac-find-index' checkElem ?hole = do
  def (quote Any)
    ( _ ∷ _ ∷ _
    ∷ vArg (def (quote _≡_) (_ ∷ _ ∷ vArg `x ∷ []))
    ∷ vArg `xs ∷ []) ← inferNormalisedType ?hole
    where g → do
            ensureNoMetas g
            typeError $ termErr g ∷ strErr "!= _ ∈ _" ∷ []
  nometaSpine `xs
  checkElem `x
  choice (map (unify ?hole) (indices `xs)) <|> withNormalisation true do
    typeError $ termErr `x ∷ strErr "not found in" ∷ termErr `xs ∷ []

tac-find-index : Tactic
tac-find-index = tac-find-index' (λ _ → return _)

private
  prove-all : Tactic → Term → Term → TC ⊤
  prove-all tac (_ `∷ `xs) ?hole = do
    ?ix  ← newMeta!
    ?ixs ← newMeta!
    unify ?hole (con₂ (quote All._∷_) ?ix ?ixs)
    tac ?ix
    prove-all tac `xs ?ixs
  prove-all _ _ ?hole = unify ?hole (con₀ (quote All.[]))

tac-all : Tactic → Tactic
tac-all tac ?hole = do
  g@(def (quote All) (_ ∷ _ ∷ _ ∷ _ ∷ vArg `xs ∷ [])) ← inferNormalisedType ?hole
    where g → do
            ensureNoMetas g
            typeError $ termErr g ∷ strErr "!= All _ _" ∷ []
  nometaSpine `xs
  prove-all tac `xs ?hole <|>
    typeError (strErr "Can't prove" ∷ termErr g ∷ [])

-- macro subl = tac-all tac-find-index

-- macro ix = tac-find-index
