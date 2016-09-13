module AComega where

open import Utilities

-- Axiom of countable choice.

ACω : Set₁
ACω = 
  {X : Set}(P : ℕ → X → Set)(r : (n : ℕ) → ∥ Σ X (λ x → P n x) ∥) → 
  ∥ Σ (ℕ → X) (λ f → (n : ℕ) → P n (f n)) ∥

postulate 
  acω : ACω

ACω₂ : Set₁
ACω₂ = (P : ℕ → Set)(r : (n : ℕ) → ∥ P n ∥) → ∥ ((n : ℕ) → P n) ∥

ACco : Set₁
ACco = {X : Set} → Stream ∥ X ∥ → ∥ Stream X ∥ 

ACω₂→ACco : ACω₂ → ACco
ACω₂→ACco p xs = map∥ right (p _ (left xs))

ACω→ACω₂ : ACω → ACω₂
ACω→ACω₂ acω P r = map∥ proj₂ s
  where
    s : ∥ Σ (ℕ → ⊤) (λ f → (n : ℕ) → P n) ∥
    s = acω _ (λ n → map∥ (λ p → _ , p) (r n))

ACω₂→ACω : ACω₂ → ACω
ACω₂→ACω acω₂ P r = map∥ (λ f → proj₁ ∘ f , proj₂ ∘ f) (acω₂ _ r)

acco : ACco
acco = ACω₂→ACco (ACω→ACω₂ acω)
