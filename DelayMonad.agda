{-# OPTIONS --type-in-type #-}
module DelayMonad where

open import Coinduction
open import Monads
open import Sets
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Utilities

data Delay (X : Set) : Set where
  now : X → Delay X
  later : ∞ (Delay X) → Delay X

dbind : ∀{X Y} → (X → Delay Y) → Delay X → Delay Y
dbind f (now x)   = f x
dbind f (later x) = later (♯ dbind f (♭ x))

data _∼_ {X : Set} : Delay X → Delay X → Set where
  now∼ : ∀{x} → now x ∼ now x
  later∼ : ∀{dy dy'} → ∞ (♭ dy ∼ ♭ dy') → later dy ∼ later dy'

refl∼ : ∀{X}(dx : Delay X) → dx ∼ dx
refl∼ (now x)   = now∼
refl∼ (later x) = later∼ (♯ refl∼ (♭ x))

trans∼ : ∀{X}{dx dx' dx'' : Delay X} → dx ∼ dx' → dx' ∼ dx'' → dx ∼ dx''
trans∼ now∼ now∼ = now∼
trans∼ (later∼ p) (later∼ q) = later∼ (♯ trans∼ (♭ p) (♭ q))

dbindlater : ∀{X Y}(f : X → ∞ (Delay Y))(dx : Delay X)(dz : Delay Y) → 
             later (♯ (dbind (♭ ∘ f) dx)) ∼ dz →
             dbind (later ∘ f) dx ∼ dz
dbindlater f (now x) (now y) ()
dbindlater f (now x) (later y) (later∼ p) = later∼ p
dbindlater f (later x) (now y) ()
dbindlater f (later x) (later y) (later∼ p) = 
  later∼ (♯ dbindlater f (♭ x) (♭ y) (trans∼ (later∼ (♯ refl∼ (dbind (♭ ∘ f) (♭ x)))) (♭ p)))

{-
dbindlater : ∀{X Y}(f : X → ∞ (Delay Y))(dx : Delay X)(dz : Delay Y) → 
             dbind (♭ ∘ f) dx ∼ dz →
             dbind (later ∘ f) dx ∼ later (♯ dz)
dbindlater f (now x) dz p = later∼ (♯ p)
dbindlater f (later x) (later dz) (later∼ p) = 
  later∼ (♯ trans∼ (dbindlater f (♭ x) (♭ dz) (♭ p)) (later∼ (♯ refl∼ (♭ dz))))
-}
-- later∼ (♯ (dbindlater f (♭ x) (♭ z) (♭ p)))
{-
dbindlater : ∀{X Y}(f : X → ∞ (Delay Y))(dx : Delay X) → 
             dbind (later ∘ f) dx ∼ later (♯ (dbind (♭ ∘ f) dx))
dbindlater f (now x) = later∼ (♯ {!!})
dbindlater f (later x) = later∼ (♯ trans∼ (dbindlater f (♭ x)) (later∼ (♯ refl∼)))
-}

data _↓_ {X : Set} : Delay X → X → Set where
  now↓ : ∀{y} → now y ↓ y
  later↓ : ∀{dy y} → (♭ dy) ↓ y → later dy ↓ y

data _≈_ {X : Set} : Delay X → Delay X → Set where
  ↓≈ : ∀{dy dy' y} → dy ↓ y → dy' ↓ y → dy ≈ dy'
  later≈ : ∀{dy dy'} → ∞ (♭ dy ≈ ♭ dy') → later dy ≈ later dy'

postulate quotient : ∀{X}{dx dx' : Delay X} → dx ≈ dx' → dx ≅ dx'

refl≈ : ∀{X}{dx : Delay X} → dx ≈ dx
refl≈ {dx = now x}    = ↓≈ now↓ now↓
refl≈ {dx = later dx} = later≈ (♯ refl≈)
{-
trans≈ : ∀{X}{dx dx' dx'' : Delay X} → dx ≈ dx' → dx' ≈ dx'' → dx ≈ dx''
trans≈ p q = {!!}
-}
dlaw1 : ∀{X}(dx : Delay X) → dbind now dx ≈ dx
dlaw1 (now x) = refl≈
dlaw1 (later dx) = later≈ (♯ dlaw1 (♭ dx))

--dlaw2 holds definitionally

dlaw3 : ∀{X Y Z}{f : X → Delay Y} {g : Y → Delay Z}(dx : Delay X) → 
        dbind (dbind g ∘ f) dx ≈ dbind g (dbind f dx)
dlaw3 {f = f}{g = g} (now x)   = refl≈
dlaw3 {f = f}{g = g} (later x) = later≈ (♯ dlaw3 (♭ x))


DelayM : Monad Sets
DelayM = record { 
  T    = Delay; 
  η    = now; 
  bind = dbind; 
  law1 = ext (quotient ∘ dlaw1); 
  law2 = refl; 
  law3 = ext (quotient ∘ dlaw3) }

