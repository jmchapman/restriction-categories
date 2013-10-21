
module Monads.Delay.Order where

open import Monads.Delay
open import Coinduction
open import Relation.Binary.HeterogeneousEquality

-- Convergence order

data _⊑_ {X : Set} : Delay X → Delay X → Set where
  ⊑now : ∀{x dx dy} → dx ↓ x → dy ↓ x → dx ⊑ dy
  ⊑later : ∀{dx dy} → ∞ (♭ dx ⊑ ♭ dy) → later dx ⊑ later dy
  ⊑leftlater : ∀{dx dy} → ∞ (♭ dx ⊑ dy) → later dx ⊑ dy

≈subrel⊑ : ∀{X}{dx dy : Delay X} → dx ≈ dy → dx ⊑ dy
≈subrel⊑ (↓≈ p q) = ⊑now p q
≈subrel⊑ (later≈ p) = ⊑later (♯ (≈subrel⊑ (♭ p)))

⊑implies↓ : ∀{X}{dx dy : Delay X} → dx ⊑ dy → ∀ {x} → dx ↓ x → dy ↓ x
⊑implies↓ (⊑now now↓ p) now↓ = p
⊑implies↓ (⊑now (later↓ p) p') (later↓ q) with unique↓ p q
⊑implies↓ (⊑now (later↓ p) p') (later↓ q) | refl = p'
⊑implies↓ (⊑later p) (later↓ q) = later↓ (⊑implies↓ (♭ p) q)
⊑implies↓ (⊑leftlater p) (later↓ q) = ⊑implies↓ (♭ p) q

↓implies⊑ : ∀{X}{dx dy : Delay X} → (∀{x} → dx ↓ x → dy ↓ x) → dx ⊑ dy
↓implies⊑ {X} {now x} p = ⊑now now↓ (p now↓)
↓implies⊑ {X} {later dx} p = ⊑leftlater (♯ (↓implies⊑ (λ q → p (later↓ q))))

later⊑prop : ∀{X}{dx : Delay X}{dy} → dx ⊑ later dy → dx ⊑ ♭ dy
later⊑prop (⊑now p (later↓ q)) = ⊑now p q
later⊑prop (⊑later p) = ⊑leftlater p
later⊑prop (⊑leftlater p) = ⊑leftlater (♯ (later⊑prop (♭ p)))

refl⊑ : ∀{X}{dx : Delay X} → dx ⊑ dx
refl⊑ {X} {now x} = ⊑now now↓ now↓
refl⊑ {X} {later dx} = ⊑later (♯ refl⊑)

antisym⊑ : ∀{X}{dx dy : Delay X} → dx ⊑ dy → dy ⊑ dx → dx ≈ dy
antisym⊑ (⊑now p p') q = ↓≈ p p'
antisym⊑ (⊑later p) (⊑now q q') = ↓≈ q' q
antisym⊑ (⊑later p) (⊑later q) = later≈ (♯ (antisym⊑ (♭ p) (♭ q)))
antisym⊑ (⊑later p) (⊑leftlater q) = 
  later≈ (♯ (antisym⊑ (♭ p) (later⊑prop (♭ q))))
antisym⊑ (⊑leftlater p) (⊑now q q') = ↓≈ q' q
antisym⊑ (⊑leftlater p) (⊑later q) = 
  later≈ (♯ (antisym⊑ (later⊑prop (♭ p)) (♭ q)))
antisym⊑ (⊑leftlater p) (⊑leftlater q) = 
  later≈ (♯ (antisym⊑ (later⊑prop (♭ p)) (later⊑prop (♭ q))))

trans⊑ : ∀{X}{dx dy dz : Delay X} → dx ⊑ dy → dy ⊑ dz → dx ⊑ dz
trans⊑ (⊑now p p') (⊑now q q') with unique↓ p' q
trans⊑ (⊑now p p') (⊑now q q') | refl = ⊑now p q'
trans⊑ (⊑now now↓ (later↓ p')) (⊑later q) = 
  ⊑now now↓ (later↓ (⊑implies↓ (♭ q) p'))
trans⊑ (⊑now (later↓ p) (later↓ p')) (⊑later q) = 
  ⊑later (♯ (trans⊑ (⊑now p p') (♭ q)))
trans⊑ (⊑now now↓ (later↓ p')) (⊑leftlater q) = 
  ⊑now now↓ (⊑implies↓ (♭ q) p')
trans⊑ (⊑now (later↓ p) (later↓ p')) (⊑leftlater q) = 
  ⊑leftlater (♯ (trans⊑ (⊑now p p') (♭ q)))
trans⊑ (⊑later p) (⊑now (later↓ q) q') = 
  ⊑leftlater (♯ (trans⊑ (♭ p) (⊑now q q')))
trans⊑ (⊑later p) (⊑later q) = ⊑later (♯ (trans⊑ (♭ p) (♭ q)))
trans⊑ (⊑later p) (⊑leftlater q) = ⊑leftlater (♯ (trans⊑ (♭ p) (♭ q)))
trans⊑ (⊑leftlater p) q = ⊑leftlater (♯ (trans⊑ (♭ p) q))

_map⊑_ : {X Y : Set} → (X → Delay Y) → (X → Delay Y) → Set
f map⊑ g = ∀ x → f x ⊑ g x


{-

-- Order equivalence

open import RestrictionCat
open import RestrictionDelay
open RestCat DelayR
open import Order DelayR
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Utilities

⊑→≤ : ∀{X}{dx dy : Delay X} → dx ⊑ dy → dcomp dx dy ≈ dx
⊑→≤ (⊑now now↓ now↓) = ↓≈ now↓ now↓
⊑→≤ (⊑now now↓ (later↓ q)) = ↓≈ (later↓ q) now↓
⊑→≤ (⊑now (later↓ p) now↓) = later≈ (♯ (⊑→≤ (⊑now p now↓)))
⊑→≤ (⊑now (later↓ p) (later↓ q)) = later≈ (♯ (⊑→≤ (⊑now p q)))
⊑→≤ (⊑later p) = later≈ (♯ (⊑→≤ (♭ p)))
⊑→≤ {dy = now x} (⊑leftlater p) = later≈ (♯ (⊑→≤ (♭ p)))
⊑→≤ {dy = later dy} (⊑leftlater p) = later≈ (♯ (⊑→≤ (later⊑prop (♭ p))))

map⊑→≤' : ∀{X Y}{f g : X → Delay Y} → f map⊑ g → (x : X) → 
          dbind g (drest f x) ≅ f x
map⊑→≤' {f = f}{g = g} p x = 
  proof
  dbind g (drest f x)
  ≅⟨ cong (dbind g) (drest≅ x f) ⟩
  dbind g (dbind (λ z → now x) (f x))
  ≅⟨ sym (compdrest {f = g} {g = f} x) ⟩
  dbind (λ _ → g x) (f x)
  ≅⟨ quotient (sym≈ (dcomp≈dbind {_}{_}{f x})) ⟩
  dcomp (f x) (g x)
  ≅⟨ quotient (⊑→≤ (p x)) ⟩
  f x
  ∎

map⊑→≤ : ∀{X Y}{f g : X → Delay Y} → f map⊑ g → f ≤ g
map⊑→≤ p = ext (map⊑→≤' p)

≤→⊑ : ∀{X}{dx dy : Delay X} → dcomp dx dy ≈ dx → dx ⊑ dy
≤→⊑ {X} {now x} (↓≈ p q) = ⊑now q p
≤→⊑ {X} {later dx} {now x} (↓≈ (later↓ p) (later↓ q)) = 
  ⊑leftlater (♯ (≤→⊑ (↓≈ p q)))
≤→⊑ {X} {later dx} {now x} (later≈ p) = ⊑leftlater (♯ (≤→⊑ (♭ p)))
≤→⊑ {X} {later dx} {later dy} (↓≈ (later↓ p) (later↓ q)) = 
  ⊑later (♯ (≤→⊑ (↓≈ p q)))
≤→⊑ {X} {later dx} {later dy} (later≈ p) = ⊑later (♯ ≤→⊑ (♭ p))

≤→map⊑ : ∀{X Y}{f g : X → Delay Y} → f ≤ g → f map⊑ g
≤→map⊑ {f = f}{g = g} p x = ≤→⊑ 
  (subst (λ y → y ≈ f x) 
         (proof
          f x
          ≅⟨ cong (λ h → h x) (sym p) ⟩
          dbind g (drest f x)
          ≅⟨ cong (dbind g) (drest≅ x f) ⟩
          dbind g (dbind (λ z → now x) (f x))
          ≅⟨ sym (compdrest {f = g} {g = f} x) ⟩
          dbind (λ _ → g x) (f x)
          ≅⟨ quotient (sym≈ (dcomp≈dbind {_}{_}{f x})) ⟩
          dcomp (f x) (g x)
          ∎)
         refl≈)

-}

