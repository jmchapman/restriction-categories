
module Monads.Delay.Decision where

open import Monads.Delay
open import Coinduction
open import RestrictionCat
open import Categories
open import Monads.Kleisli
open Cat (Kl DelayM)
open import RestrictionDelay
open RestCat DelayR
open import Data.Sum hiding (map)
open import Utilities

{-
ι₀ : {A B : Set} → A → Delay (A ⊎ B)
ι₀ a = now (inj₁ a)  

ι₁ : {A B : Set} → B → Delay (A ⊎ B)
ι₁ b = now (inj₂ b)

const⊎ : {A B C : Set} → Delay (B ⊎ C) → A → Delay (A ⊎ A)
const⊎ (now (inj₁ b)) a = now (inj₁ a)
const⊎ (now (inj₂ c)) a = now (inj₂ a)
const⊎ (later bc) a = later (♯ (const⊎ (♭ bc) a))

⟨_⟩ : {A B C : Set} → (A → Delay (B ⊎ C)) → A → Delay (A ⊎ A)
⟨ f ⟩ a = const⊎ (f a) a

_m⊎_ : {A A' B B' : Set} → (A → Delay B) → (A' → Delay B') → A ⊎ A' → 
       Delay (B ⊎ B') 
(f m⊎ g) (inj₁ a) = comp ι₀ f a
(f m⊎ g) (inj₂ a') = comp ι₁ g a'

∇ : {A : Set} → A ⊎ A → Delay A
∇ (inj₁ a) = now a
∇ (inj₂ a) = now a

Dec1' : ∀{A B C}(bc : Delay (B ⊎ C))(a : A) → 
        comp ∇ (const⊎ bc) a ≈ map proj₁ (str (a , bc))
Dec1' (now (inj₁ b)) a = ↓≈ now↓ now↓
Dec1' (now (inj₂ c)) a = ↓≈ now↓ now↓
Dec1' (later bc) a = later≈ (♯ (Dec1' (♭ bc) a))

Dec1 : ∀{A B C}(f : A → Delay (B ⊎ C))(a : A) → comp ∇ ⟨ f ⟩ a ≈ rest f a
Dec1 f a = Dec1' (f a) a

compι₀↓ : ∀{A B}(c : Delay A){a : A} → c ↓ a → dbind (ι₀ {B = B}) c ↓ inj₁ a
compι₀↓ .(now a) {a} now↓ = now↓
compι₀↓ .(later dy) (later↓ {dy} p) = later↓ (compι₀↓ (♭ dy) p)

compι₁↓ : ∀{A B}(c : Delay B){b : B} → c ↓ b → dbind (ι₁ {A = A}) c ↓ inj₂ b
compι₁↓ .(now b) {b} now↓ = now↓
compι₁↓ .(later dy) (later↓ {dy} p) = later↓ (compι₁↓ (♭ dy) p)

Dec2' : ∀{A B C}(f : A → Delay (B ⊎ C))(bc : Delay (B ⊎ C))(a : A) → bc ≈ f a → 
        comp (f m⊎ f) (const⊎ bc) a ≈ comp (ι₀ m⊎ ι₁) (λ _ → bc) a
Dec2' f bc a p with f a | inspect f a
Dec2' f (now (inj₁ b)) a (↓≈ {.(now (inj₁ b))} {dy'} now↓ x₂) | .dy' | [ eq ] = 
  ↓≈ (≈↓ (subst (λ x → now (inj₁ (inj₁ b)) ≈ dbind ι₀ x) 
                (sym eq) 
                (↓≈ now↓ (compι₀↓ dy' x₂)))
          now↓) 
      now↓

Dec2' f (now (inj₂ c)) a (↓≈ {.(now (inj₂ c))} {dy'} now↓ x₁) | .dy' | [ eq ] = 
  ↓≈ (≈↓ (subst (λ x → now (inj₂ (inj₂ c)) ≈ dbind ι₁ x) 
                (sym eq) 
                (↓≈ now↓ (compι₁↓ dy' x₁))) 
          now↓) 
      now↓

Dec2' f (later x) a (↓≈ {.(later x)} {dy'} (later↓ p) q) | .dy' | [ eq ] = 
  later≈ (♯ (Dec2' f (♭ x) a (subst (_≈_ (♭ x)) (sym eq) (↓≈ p q))))
Dec2' f (later .dy) a (later≈ {dy} {dy'} p) | .(later dy') | [ eq ] = 
  later≈ (♯ (Dec2' f (♭ dy) a (trans≈ (♭ p) (subst (_≈_ (♭ dy')) (sym eq) (trans≈ laterlem (later≈ (♯ refl≈)))))))

Dec2 : ∀{A B C}(f : A → Delay (B ⊎ C))(a : A) → 
       comp (f m⊎ f) ⟨ f ⟩ a ≈ comp (ι₀ m⊎ ι₁) f a
Dec2 f a = Dec2' f _ a refl≈

-}
