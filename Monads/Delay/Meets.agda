
module Monads.Delay.Meets where

open import Coinduction
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open ≅-Reasoning renaming (begin_ to proof_)
open import Monads.Delay
open import RestrictionDelay
open import RestrictionCat
open RestCat DelayR
open import Order DelayR
open Meets
open import Relation.Binary
open import Relation.Nullary.Core

-- Meets

_≡_ : ∀{a}{A B : Set a} → A → B → Set a
a ≡ b = a ≅ b

-- with decidability of equality in codomains

dmeet-aux : ∀{X}{_≟_ : Decidable {A = X} _≡_} → Delay X → Delay X → Delay X
dmeet-aux {X}{_≟_} (now x) (now y) with x ≟ y
dmeet-aux {X}{_≟_} (now x) (now .x) | yes refl = now x
dmeet-aux {X}{_≟_} (now x) (now y) | no ¬p = 
  later (♯ (dmeet-aux {X}{_≟_} (now x) (now y)))
dmeet-aux {X}{_≟_} (now x) (later dy) = 
  later (♯ (dmeet-aux {X}{_≟_} (now x) (♭ dy)))
dmeet-aux {X}{_≟_} (later dx) (now y) = 
  later (♯ (dmeet-aux {X}{_≟_} (♭ dx) (now y)))
dmeet-aux {X}{_≟_} (later dx) (later dy) = 
  later (♯ (dmeet-aux {X}{_≟_} (♭ dx) (♭ dy)))

dmeet : {X Y : Set}{_≟_ : Decidable {A = Y}{B = Y} _≡_}
        (f g : X → Delay Y) → X → Delay Y
dmeet {X}{Y}{_≟_} f g x = dmeet-aux {Y}{_≟_} (f x) (g x)

{-
-- with semidecidability of equality in codomains 

data SemiDec {p} (P : Set p) : Set p where
  yes  : ( p :   P) → SemiDec P
  no   : (¬p : ¬ P) → SemiDec P
  wait : SemiDec P → SemiDec P

SemiDecidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
SemiDecidable _∼_ = ∀ x y → SemiDec (x ∼ y)

dmeet-aux : ∀{X}{_≟_ : SemiDecidable {A = X} _≡_} → Delay X → Delay X → Delay X
dmeet-aux {X}{_≟_} (now x) (now y) with x ≟ y
dmeet-aux {X}{_≟_} (now x) (now .x) | yes refl = now x
dmeet-aux {X}{_≟_} (now x) (now y)  | no ¬p = 
  later (♯ (dmeet-aux {X}{_≟_} (now x) (now y)))
dmeet-aux {X}{_≟_} (now x) (now y)  | wait q = 
  later (♯ (dmeet-aux {X}{_≟_} (now x) (now y)))
dmeet-aux {X}{_≟_} (now x) (later dy) = 
  later (♯ (dmeet-aux {X}{_≟_} (now x) (♭ dy)))
dmeet-aux {X}{_≟_} (later dx) (now y) = 
  later (♯ (dmeet-aux {X}{_≟_} (♭ dx) (now y)))
dmeet-aux {X}{_≟_} (later dx) (later dy) = 
  later (♯ (dmeet-aux {X}{_≟_} (♭ dx) (♭ dy)))

dmeet : {X Y : Set}{_≟_ : SemiDecidable {A = Y}{B = Y} _≡_}
       (f g : X → Delay Y) → X → Delay Y
dmeet {X}{Y}{_≟_} f g x = dmeet-aux {Y}{_≟_} (f x) (g x)
-}

dMt1-aux  : ∀{X}{_≟_ : Decidable {A = X} _≡_}(dx : Delay X) → 
            dmeet-aux {X}{_≟_} dx dx ≈ dx
dMt1-aux {X}{_≟_} (now x) with x ≟ x
dMt1-aux (now x) | yes refl = ↓≈ now↓ now↓
dMt1-aux (now x) | no ¬p with ¬p refl
dMt1-aux (now x) | no ¬p | ()
dMt1-aux (later dx) = later≈ (♯ (dMt1-aux (♭ dx)))

dMt1  : ∀{X Y}{_≟_ : Decidable {A = Y}{B = Y} _≡_}{f : X → Delay Y} → 
        (x : X) → dmeet {X}{Y}{_≟_} f f x ≅ f x
dMt1 {f = f} x = quotient (dMt1-aux (f x))

dMt2a-aux' : ∀{X}{_≟_ : Decidable {A = X} _≡_}{dx dy : Delay X} →
             dmeet-aux {X}{_≟_} dx dy ≈ 
             dcomp (dmeet-aux {X}{_≟_} dx dy) dy
dMt2a-aux' {X}{_≟_}{now x}{now y} with x ≟ y
dMt2a-aux' {X}{_≟_}{now x}{now .x} | yes refl = ↓≈ now↓ now↓
dMt2a-aux' {X}{_≟_}{now x}{now y} | no ¬p = 
  later≈ (♯ dMt2a-aux' {_}{_}{now x}{now y})
dMt2a-aux' {X}{_≟_}{later dx}{now y} = later≈ (♯ dMt2a-aux' {_}{_}{♭ dx})
dMt2a-aux' {X} {_≟_}{now x}{later dy} = 
  later≈ (♯ dMt2a-aux' {_}{_}{now x}{♭ dy})
dMt2a-aux' {X} {_≟_}{later dx}{later dy} = 
  later≈ (♯ dMt2a-aux' {_}{_}{♭ dx}{♭ dy})

dMt2a-aux : ∀{X}{_≟_ : Decidable {A = X} _≡_}{dx dy : Delay X} →
            dmeet-aux {X}{_≟_} dx dy ≈ 
            dbind (λ _ → dy) (dmeet-aux {X}{_≟_} dx dy)
dMt2a-aux {X}{_≟_}{dx}{dy} = 
  trans≈ (dMt2a-aux' {_}{_}{dx}{dy}) 
         (dcomp≈dbind {_}{_}{dmeet-aux {_}{_≟_} dx dy})

dMt2a : ∀{X Y}{_≟_ : Decidable {A = Y}{B = Y} _≡_}{f g : X → Delay Y} →
        dmeet {X}{Y}{_≟_} f g ≤ g
dMt2a {X}{Y}{_≟_}{f}{g} = ext (λ x → 
  proof 
  dbind g (drest (dmeet f g) x)
  ≅⟨ cong (dbind g) (drest≅ x (dmeet f g)) ⟩
  dbind g (dbind (λ z → now x) (dmeet f g x))
  ≅⟨ sym (compdrest {f = g}{g = dmeet f g} x) ⟩
  dbind (λ _ → g x) (dmeet f g x)
  ≅⟨ quotient (sym≈ (dMt2a-aux {dx = f x}{dy = g x})) ⟩
  dmeet f g x
  ∎)

-- dMt2b is similar
