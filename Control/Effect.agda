
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

data EFFECT : Set₂ where
  mkEff : Set → Effect → EFFECT

private
  variable
    eff eff₁ eff₂ eff₃ effᵢ effᵢ′ : List EFFECT
    effₒ effₒ′ : A → List EFFECT

updateAt : x ∈ xs → Set → List EFFECT → List EFFECT
updateAt _ _ [] = []
updateAt (zero _) B (mkEff _ E ∷ es) = mkEff B E ∷ es
updateAt (suc i) B (e ∷ es) = e ∷ updateAt i B es

updateWith : (ys′ xs : List EFFECT) → ys ⊆ xs → List EFFECT
updateWith []        xs inc = xs
updateWith (x ∷ ys′) xs [] = xs
updateWith (mkEff R E ∷ ys′) xs (i ∷ inc) = updateAt i R (updateWith ys′ xs inc)

record Handler (E : Effect) (M : Set → Set) : Set₁ where
  field
    handle : Resᵢ → (eff : E A Resᵢ Resₒ) →
             (∀ x → Resₒ x → M B) → M B

open Handler ⦃ ... ⦄ public

updateResTy : (x : A) → mkEff Resᵢ E ∈ eff → E A Resᵢ Resₒ → List EFFECT
updateResTy {eff = mkEff _ E ∷ eff} {Resₒ = Resₒ} x zero! e = mkEff (Resₒ x) E ∷ eff
updateResTy {eff = ef ∷ eff} x (suc i) e = ef ∷ updateResTy x i e

data EffM (M : Set → Set) (A : Set) (effᵢ : List EFFECT) : (A → List EFFECT) → Set₂ where
  ret : (x : A) → EffM M A effᵢ (λ _ → effᵢ)
  bindE : EffM M B effᵢ effₒ → ((x : B) → EffM M A (effₒ x) effₒ′) → EffM M A effᵢ effₒ′
  callE : (i : mkEff Resᵢ E ∈ effᵢ) (e : E A Resᵢ Resₒ) →
          EffM M A effᵢ (λ x → updateResTy x i e)
  liftE : (inc : effᵢ′ ⊆ effᵢ) → EffM M A effᵢ′ effₒ →
          EffM M A effᵢ (λ x → updateWith (effₒ x) effᵢ inc)
  newE : ⦃ h : Handler E M ⦄ (e : EFFECT) → Res →
         ⦃ eq : e ≡ mkEff Res E ⦄ →
         EffM M A (e ∷ effᵢ) (λ _ → e ∷ effᵢ) → EffM M A effᵢ (λ _ → effᵢ)

NondepEffM : (Set → Set) → Set → List EFFECT → List EFFECT → Set₂
NondepEffM M A effᵢ effₒ = EffM M A effᵢ λ _ → effₒ

syntax NondepEffM M A effᵢ effₒ = Eff M [ effᵢ => effₒ ] A
syntax EffM M A effᵢ (λ x → effₒ) = Eff M [ effᵢ => x ∙ effₒ ] A

bindEff : EffM M B effᵢ effₒ → ((x : B) → EffM M A (effₒ x) effₒ′) → EffM M A effᵢ effₒ′
bindEff = bindE

thenEff : EffM M B effᵢ effₒ → ({x : B} → EffM M A (effₒ x) effₒ′) → EffM M A effᵢ effₒ′
thenEff m m′ = bindE m λ x → m′

data HEnv (M : Set → Set) : List EFFECT → Set₁ where
  []  : HEnv M []
  _∷_ : ⦃ h : Handler E M ⦄ → Res → HEnv M eff → HEnv M (mkEff Res E ∷ eff)

envElem : ∀ {e} → e ∈ eff → HEnv M eff → HEnv M (e ∷ [])
envElem zero!   (x ∷ env) = x ∷ []
envElem (suc i) (_ ∷ env) = envElem i env

dropEnv : effᵢ ⊆ effᵢ′ → HEnv M effᵢ′ → HEnv M effᵢ
dropEnv []       env = []
dropEnv (i ∷ is) env =
  case envElem i env of λ where
    (r ∷ []) → r ∷ dropEnv is env

replaceEnvAt : (y : A) (i : x ∈ xs) → HEnv M ys → HEnv M (updateAt i A ys)
replaceEnvAt y i [] = []
replaceEnvAt y zero!   (x ∷ env) = y ∷ env
replaceEnvAt y (suc i) (x ∷ env) = x ∷ replaceEnvAt y i env

rebuildEnv : HEnv M eff₁ → (inc : eff₂ ⊆ eff) → HEnv M eff → HEnv M (updateWith eff₁ eff inc)
rebuildEnv [] _ env = env
rebuildEnv (x ∷ env′) [] env = env
rebuildEnv (x ∷ env′) (i ∷ inc) env = replaceEnvAt x i (rebuildEnv env′ inc env)

execEff : HEnv M effᵢ → (i : mkEff Resᵢ E ∈ effᵢ) (e : E A Resᵢ Resₒ) →
          ((x : A) → HEnv M (updateResTy x i e) → M B) -> M B
execEff (r ∷ env) zero!   e k = handle r e λ x r′ → k x (r′ ∷ env)
execEff (r ∷ env) (suc i) e k = execEff env i e λ x env′ → k x (r ∷ env′)

runEff : HEnv M effᵢ → EffM M A effᵢ effₒ →
         ((x : A) → HEnv M (effₒ x) → M B) → M B
runEff env (ret x)       k = k x env
runEff env (bindE m f)   k = runEff env m λ x env′ → runEff env′ (f x) k
runEff env (callE i eff) k = execEff env i eff k
runEff env (liftE p m)   k = runEff (dropEnv p env) m λ x env′ → k x (rebuildEnv env′ p env)
runEff env (newE e r ⦃ refl ⦄ m)  k = runEff (r ∷ env) m (λ { x (_ ∷ env′) → k x env′ })

returnEff : A → EffM M A effᵢ (λ _ → effᵢ)
returnEff x = ret x

-- call : (e : E A Resᵢ Resₒ) → EffM A (mkEff Resᵢ E ∷ []) (λ x → mkEff (Resₒ x) E ∷ [])
-- call e = callE zero! e

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
  lift = apply-tac-con (quote liftE) tac-subset
  call = apply-tac-con (quote callE) tac-find-index

  -- bindEff = apply-tac-def (quote bindEff′) tac-subset
  -- thenEff = apply-tac-def (quote thenEff′) tac-subset
