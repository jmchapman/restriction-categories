
module Monads.Delay.Independence where

open import Monads.Delay
open import Coinduction
open import Data.Product hiding (map)
open import Data.Empty renaming (⊥ to ∅)

{-
-- Independence (also called disjointness)

data _d⊥_  {X Y : Set} : Delay X → Delay Y → Set where
  now⊥later   : ∀{x dy} → ∞ (now x d⊥ (♭ dy)) → now x d⊥ later dy
  later⊥now   : ∀{dx y} → ∞ ((♭ dx) d⊥ now y) → later dx d⊥ now y
  later⊥later : ∀{dx dy} → ∞ ((♭ dx) d⊥ (♭ dy)) → later dx d⊥ later dy

_⊥_ : ∀{X Y} → (X → Delay X) → (X → Delay Y) → Set
f ⊥ g = ∀ x → f x d⊥ g x

d⊥sym : ∀{X Y}{dx : Delay X}{dy : Delay Y} → dx d⊥ dy → dy d⊥ dx
d⊥sym (now⊥later p) = later⊥now (♯ (d⊥sym (♭ p)))
d⊥sym (later⊥now p) = now⊥later (♯ (d⊥sym (♭ p)))
d⊥sym (later⊥later p) = later⊥later (♯ (d⊥sym (♭ p)))

d⊥→∅ : ∀{X Y}{dx dy}{x : X}{y : Y} → dx ↓ x → dy ↓ y → dx d⊥ dy → ∅
d⊥→∅ now↓ (later↓ q) (now⊥later r) = d⊥→∅ now↓ q (♭ r)
d⊥→∅ (later↓ p) now↓ (later⊥now r) = d⊥→∅ p now↓ (♭ r)
d⊥→∅ (later↓ p) (later↓ q) (later⊥later r) = d⊥→∅ p q (♭ r)

d⊥≈never : ∀{X Y}{dx : Delay X}{y : Y} → dx d⊥ now y → dx ≈ never
d⊥≈never (later⊥now p) = later≈ (♯ (d⊥≈never (♭ p)))

{-
d⊥-right-compat : ∀{X Y}{dx : Delay X}{dy dy' : Delay Y} → dx d⊥ dy → dy ≈ dy' →
                  dx d⊥ dy'
d⊥-right-compat (now⊥later p) (↓≈ (later↓ q) now↓) = ⊥-elim (d⊥→∅ now↓ q (♭ p))
d⊥-right-compat (now⊥later p) (↓≈ (later↓ q) (later↓ r)) = 
  now⊥later (♯ (d⊥-right-compat (♭ p) (↓≈ q r)))
d⊥-right-compat (now⊥later p) (later≈ q) = 
  now⊥later (♯ (d⊥-right-compat (♭ p) (♭ q)))
d⊥-right-compat (later⊥now p) (↓≈ now↓ now↓) = later⊥now (♯ (♭ p))
d⊥-right-compat (later⊥now p) (↓≈ now↓ (later↓ q)) = 
  later⊥later (♯ (d⊥-right-compat (♭ p) (↓≈ now↓ q)))
d⊥-right-compat (later⊥later p) (↓≈ (later↓ q) now↓) = 
  later⊥now (♯ (d⊥-right-compat (♭ p) (↓≈ q now↓)))
d⊥-right-compat (later⊥later p) (↓≈ (later↓ q) (later↓ r)) = 
  later⊥later (♯ (d⊥-right-compat (♭ p) (↓≈ q r)))
d⊥-right-compat (later⊥later p) (later≈ q) = 
  later⊥later (♯ (d⊥-right-compat (♭ p) (♭ q)))
-}

d⊥-cong : ∀{X Y}{dx dx' : Delay X}{dy dy' : Delay Y} → dx ≈ dx' → dy ≈ dy' → 
          dx d⊥ dy → dx' d⊥ dy'
d⊥-cong (↓≈ now↓ p) (↓≈ (later↓ q) q') (now⊥later r) = 
  ⊥-elim (d⊥→∅ now↓ q (♭ r))
d⊥-cong (↓≈ now↓ now↓) (later≈ q) (now⊥later r) = 
  now⊥later (♯ (d⊥-cong (↓≈ now↓ now↓) (♭ q) (♭ r)))
d⊥-cong (↓≈ now↓ (later↓ p)) (later≈ q) (now⊥later r) = 
  later⊥later (♯ (d⊥-cong (↓≈ now↓ p) (♭ q) (♭ r)))
d⊥-cong (↓≈ (later↓ p) p') (↓≈ now↓ q) (later⊥now r) = 
  ⊥-elim (d⊥→∅ p now↓ (♭ r))
d⊥-cong (later≈ p) (↓≈ now↓ now↓) (later⊥now r) = 
  later⊥now (♯ (d⊥-cong (♭ p) (↓≈ now↓ now↓) (♭ r)))
d⊥-cong (later≈ p) (↓≈ now↓ (later↓ q)) (later⊥now r) = 
  later⊥later (♯ (d⊥-cong (♭ p) (↓≈ now↓ q) (♭ r)))
d⊥-cong (↓≈ (later↓ p) p') (↓≈ (later↓ q) q') (later⊥later r) = 
  ⊥-elim (d⊥→∅ p q (♭ r))
d⊥-cong (↓≈ (later↓ p) now↓) (later≈ q) (later⊥later r) = 
  now⊥later (♯ (d⊥-cong (↓≈ p now↓) (♭ q) (♭ r)))
d⊥-cong (↓≈ (later↓ p) (later↓ p')) (later≈ q) (later⊥later r) = 
  later⊥later (♯ (d⊥-cong (↓≈ p p') (♭ q) (♭ r)))
d⊥-cong (later≈ p) (↓≈ (later↓ q) now↓) (later⊥later r) = 
  later⊥now (♯ (d⊥-cong (♭ p) (↓≈ q now↓) (♭ r)))
d⊥-cong (later≈ p) (↓≈ (later↓ q) (later↓ q')) (later⊥later r) = 
  later⊥later (♯ (d⊥-cong (♭ p) (↓≈ q q') (♭ r)))
d⊥-cong (later≈ p) (later≈ q) (later⊥later r) = 
  later⊥later (♯ (d⊥-cong (♭ p) (♭ q) (♭ r)))
-}

