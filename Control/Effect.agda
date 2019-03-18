
module Control.Effect where

open import Prelude
open import Container.List
open import Variables
open import Tactic.Reflection
open import Lib

Effect = (A : Set) (Resᵢ : Set) (Resₒ : A → Set) → Set₁

private
  variable
    Res Resᵢ : Set
    Resₒ : A → Set
    E : Effect

infix 6 _⊢_
data EFFECT : Set₂ where
  _⊢_ : Effect → Set → EFFECT

private
  variable
    es es₁ es₂ es₃ esᵢ esᵢ′ : List EFFECT
    esₒ esₒ′ : A → List EFFECT

infixr 4 _∧_
_∧_ : List EFFECT → List EFFECT → List EFFECT
xs ∧ ys = xs ++ ys

updateAt : x ∈ xs → Set → List EFFECT → List EFFECT
updateAt _ _ [] = []
updateAt (zero _) B (E ⊢ _ ∷ es) = E ⊢ B ∷ es
updateAt (suc i) B (e ∷ es) = e ∷ updateAt i B es

updateWith : (ys′ xs : List EFFECT) → ys ⊆ xs → List EFFECT
updateWith []        xs inc = xs
updateWith (x ∷ ys′) xs [] = xs
updateWith (E ⊢ R ∷ ys′) xs (i ∷ inc) = updateAt i R (updateWith ys′ xs inc)

record Handler (E : Effect) (M : Set → Set) : Set₁ where
  field
    handle : Resᵢ → E A Resᵢ Resₒ →
             (∀ x → Resₒ x → M B) → M B

open Handler ⦃ ... ⦄ public

updateResTy : (x : A) → E ⊢ Resᵢ ∈ es → E A Resᵢ Resₒ → List EFFECT
updateResTy {es = E ⊢ _ ∷ es} {Resₒ = Resₒ} x zero! e = E ⊢ Resₒ x ∷ es
updateResTy {es = ef ∷ es} x (suc i) e = ef ∷ updateResTy x i e

data Eff (M : Set → Set) (A : Set) (esᵢ : List EFFECT) : (A → List EFFECT) → Set₂ where

  retE  : (x : A) ⦃ eq : esᵢ ≡ esₒ x ⦄ → Eff M A esᵢ esₒ

  bindE : Eff M B esᵢ esₒ → ((x : B) → Eff M A (esₒ x) esₒ′) → Eff M A esᵢ esₒ′

  callE : (i : E ⊢ Resᵢ ∈ esᵢ) (e : E A Resᵢ Resₒ) →
          Eff M A esᵢ (λ x → updateResTy x i e)

  liftE : (inc : esᵢ′ ⊆ esᵢ) → Eff M A esᵢ′ esₒ →
          Eff M A esᵢ (λ x → updateWith (esₒ x) esᵢ inc)

  newE  : ⦃ h : Handler E M ⦄ (es : List EFFECT) → Res →
          ⦃ eq : es ≡ E ⊢ Res ∷ [] ⦄ →
          Eff M A (es ∧ esᵢ) (λ x → es ∧ esₒ x) → Eff M A esᵢ esₒ

syntax EffSyntax f i (λ x → o) = f [ i => x ∙ o ]
syntax EffSyntax-nondep f i o = f [ i => o ]
syntax EffSyntax-noupd f i = f [- i -]

EffSyntax : (A → (B → C) → D) → A → (B → C) → D
EffSyntax f = f

EffSyntax-nondep : (A → (B → C) → D) → A → C → D
EffSyntax-nondep f i o = f i (λ _ → o)

EffSyntax-noupd : (A → (B → A) → D) → A → D
EffSyntax-noupd f i = f i (λ _ → i)

bindEff : Eff M B esᵢ esₒ → ((x : B) → Eff M A (esₒ x) esₒ′) → Eff M A esᵢ esₒ′
bindEff = bindE

thenEff : Eff M B esᵢ esₒ → ({x : B} → Eff M A (esₒ x) esₒ′) → Eff M A esᵢ esₒ′
thenEff m m′ = bindE m λ x → m′

data HEnv (M : Set → Set) : List EFFECT → Set₁ where
  []  : HEnv M []
  _∷_ : ⦃ h : Handler E M ⦄ → Res → HEnv M es → HEnv M (E ⊢ Res ∷ es)

instance
  iEmptyEnv : HEnv M []
  iEmptyEnv = []

  iConsEnv : ⦃ h : Handler E M ⦄ ⦃ r : Res ⦄ ⦃ hs : HEnv M es ⦄ → HEnv M (E ⊢ Res ∷ es)
  iConsEnv ⦃ r = r ⦄ ⦃ hs ⦄ = r ∷ hs

envElem : ∀ {e} → e ∈ es → HEnv M es → HEnv M (e ∷ [])
envElem zero!   (x ∷ env) = x ∷ []
envElem (suc i) (_ ∷ env) = envElem i env

dropEnv : esᵢ ⊆ esᵢ′ → HEnv M esᵢ′ → HEnv M esᵢ
dropEnv []       env = []
dropEnv (i ∷ is) env =
  case envElem i env of λ where
    (r ∷ []) → r ∷ dropEnv is env

replaceEnvAt : (y : A) (i : x ∈ xs) → HEnv M ys → HEnv M (updateAt i A ys)
replaceEnvAt y i [] = []
replaceEnvAt y zero!   (x ∷ env) = y ∷ env
replaceEnvAt y (suc i) (x ∷ env) = x ∷ replaceEnvAt y i env

rebuildEnv : HEnv M es₁ → (inc : es₂ ⊆ es) → HEnv M es → HEnv M (updateWith es₁ es inc)
rebuildEnv [] _ env = env
rebuildEnv (x ∷ env′) [] env = env
rebuildEnv (x ∷ env′) (i ∷ inc) env = replaceEnvAt x i (rebuildEnv env′ inc env)

execEff : HEnv M esᵢ → (i : E ⊢ Resᵢ ∈ esᵢ) (e : E A Resᵢ Resₒ) →
          ((x : A) → HEnv M (updateResTy x i e) → M B) -> M B
execEff (r ∷ env) zero!   e k = handle r e λ x r′ → k x (r′ ∷ env)
execEff (r ∷ env) (suc i) e k = execEff env i e λ x env′ → k x (r ∷ env′)

runEff : HEnv M esᵢ → Eff M A esᵢ esₒ →
         ((x : A) → HEnv M (esₒ x) → M B) → M B
runEff env (retE x ⦃ refl ⦄) k = k x env
runEff env (bindE m f)   k = runEff env m λ x env′ → runEff env′ (f x) k
runEff env (callE i es) k = execEff env i es k
runEff env (liftE p m)   k = runEff (dropEnv p env) m λ x env′ → k x (rebuildEnv env′ p env)
runEff env (newE e r ⦃ refl ⦄ m)  k = runEff (r ∷ env) m (λ { x (_ ∷ env′) → k x env′ })

runE : ⦃ _ : Applicative M ⦄ ⦃ env : HEnv M esᵢ ⦄ → Eff M A esᵢ esₒ → M A
runE ⦃ env = env ⦄ e = runEff env e λ x _ → pure x

returnEff : (x : A) ⦃ eq : esᵢ ≡ esₒ x ⦄ → Eff M A esᵢ esₒ
returnEff = retE

new : ⦃ h : Handler E M ⦄ (es : List EFFECT) → Res →
      ⦃ eq : es ≡ E ⊢ Res ∷ [] ⦄ →
      Eff M A (es ∧ esᵢ) (λ _ → es ∧ esᵢ) → Eff M A esᵢ (λ _ → esᵢ)
new = newE

apply-tac-def : Name → Tactic → Tactic
apply-tac-def f tac ?hole = do
  ?p ← newMeta!
  unify ?hole (def₁ f ?p)
  tac ?p

apply-tac-con : Name → Tactic → Tactic
apply-tac-con f tac ?hole = do
  ?p ← newMeta!
  unify ?hole (con₁ f ?p)
  tac ?p

tac-subset = tac-all tac-find-index
macro subset! = tac-subset

macro
  lift_ = apply-tac-con (quote liftE) tac-subset

  call_ : Tactic
  call_ ?hole = do
    pi (arg _ `e) _ ← inferType ?hole
      where meta x _ → blockOnMeta x
            other → typeError (strErr "Not a function type:" ∷ termErr other ∷ [])
    def `E _ ← return `e
      where meta x _ → blockOnMeta x
            other → typeError (strErr "Not good:" ∷ termErr other ∷ [])
    `es ← newMeta (def₁ (quote List) (def₀ (quote EFFECT)))
    `R  ← newMeta set₀
    ?i  ← newMeta (def₂ (quote _∈_) (con₂ (quote _⊢_) (def `E []) `R) `es)
    unify ?hole (con₁ (quote callE) ?i)
    tac-find-index ?i

infix -100 call_
