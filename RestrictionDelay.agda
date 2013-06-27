module RestrictionDelay where

open import Coinduction
open import Categories
open import Monads
open import Functors
open import Monads.Kleisli
open import Sets
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open import Data.Product hiding (map)
open ≅-Reasoning renaming (begin_ to proof_)
open import RestrictionCat
open import Monads.Delay

drest : ∀{X Y} → (X → Delay Y) → X → Delay X
drest f x = map proj₁ (str (x , f x))

open Cat (Kl DelayM)

{-
data _R_ {X : Set} : Delay X → Delay X → Set where
  nowR : ∀{x} → now x R now x
  later2 : ∀{dx dx'} → ∞ (♭ dx R ♭ dx') → later (♯ (later dx)) R later dx'
-}

∼→≈ : ∀{X}{dx dy : Delay X} → dx ∼ dy → dx ≈ dy
∼→≈ p = {!!}

sym≈ : ∀{X}{dx dx' : Delay X} → dx ≈ dx' → dx' ≈ dx
sym≈ p = {!!}

trans≈ : ∀{X}{dx dx' dx'' : Delay X} → dx ≈ dx' → dx' ≈ dx'' → dx ≈ dx''
trans≈ p q = {!!}

dbind↓' : ∀{X}{dx dz : Delay X}{y : X} → dbind (λ _ → dx) dx ≈ dz → dz ↓ y → dx ↓ y
dbind↓' {X} {now .y} (↓≈ (now↓ {y}) (now↓ {.y})) now↓ = now↓
dbind↓' {X} {now .y} (↓≈ (now↓ {y}) (later↓ r)) (later↓ q) with unique↓ q r
dbind↓' {X} {now .y} (↓≈ (now↓ {y}) (later↓ r)) (later↓ q) | refl = now↓
dbind↓' {X} {later x} (↓≈ (later↓ x₁) now↓) now↓ = {!!}
dbind↓' {X} {later x} (↓≈ x₁ x₂) (later↓ q) = {!!}
dbind↓' {X} {later x} (later≈ x₁) (later↓ q) = {!!}

dbind↓'' : ∀{X}{dx dz : Delay X}{y : X} → dbind (λ _ → dx) dx ∼ dz → dz ↓ y → dx ↓ y
dbind↓'' {X} {now .y} now∼ (now↓ {y}) = now↓
dbind↓'' {X} {later x} {now z} () q
dbind↓'' {X} {later dx} p (later↓ q) = {!!}

dbind↓ : ∀{X}{dx : Delay X}{y : X} → dbind (λ _ → dx) dx ↓ y → dx ↓ y
dbind↓ {X} {now x} p = p
dbind↓ {X} {later dx} (later↓ p) = {!p!}

lemma : ∀{X}{dx dz : Delay X} → dbind (λ _ → dx) dx ≈ dz → dx ≈ dz
lemma {X} {now x} (↓≈ p q) = ↓≈ p q
lemma {X} {later dx} (↓≈ p q) = ↓≈ (dbind↓' refl≈ p) q
lemma {X} {later dx} {later dz} (later≈ p) = later≈ (♯ lemma (trans≈ (trans≈ (trans≈ (laterlem {_} {dbind (λ _ → ♭ dx) (♭ dx)}) (later≈ (♯ refl≈))) (sym≈ (∼→≈ (dbindlater _ (♭ dx))))) (♭ p)))





dR1 : ∀{X Y}{f : X → Delay Y}(x : X) → (dbind f ∘ (drest f)) x ≅ f x
dR1 {f = f} x = 
  let open Monad DelayM 
  in  proof
      dbind f (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x)))
      ≅⟨ cong (λ f' → dbind f (f' (f x)))
              (sym (law3 {f = λ y → now (x , y)} {g = now ∘ proj₁})) ⟩
      dbind f (dbind (λ _ → now x) (f x))
      ≅⟨ cong (λ f' → f' (f x)) (sym (law3 {f = λ _ → now x} {g = f})) ⟩
      dbind (λ _ → f x) (f x)
      ≅⟨ quotient {!sym≈ (lemma (f x) (dbind (λ _ → f x) (f x)) refl∼)!} ⟩
      f x 
      ∎

{-
DelayR : RestCat
DelayR = record { 
  cat  = Kl DelayM; 
  rest = drest; 
  R1   = {!Monad.law3 DelayM!}; 
  R2   = {!!}; 
  R3   = {!!}; 
  R4   = {!!} }
-}

