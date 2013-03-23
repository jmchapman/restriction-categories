{-# OPTIONS --type-in-type #-}
module PartialDelay where

open import Coinduction
open import Categories
open import Monads
open import Kleisli
open import Sets
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Equality
open ≅-Reasoning renaming (begin_ to proof_)
open import RestrictionCat

data Delay (X : Set) : Set where
  now : X → Delay X
  later : ∞ (Delay X) → Delay X

dbind : ∀{X Y} → (X → Delay Y) → Delay X → Delay Y
dbind f (now x)   = f x
dbind f (later x) = later (♯ dbind f (♭ x))

data _↓_ {X : Set} : Delay X → X → Set where
  now↓ : ∀{y} → now y ↓ y
  later↓ : ∀{dy y} → (♭ dy) ↓ y → later dy ↓ y

data _∼_ {X : Set} : Delay X → Delay X → Set where
  ↓∼ : ∀{dy dy' y y'} → dy ↓ y → dy' ↓ y' → dy ∼ dy'
  later∼ : ∀{dy dy'} → ∞ (♭ dy ∼ ♭ dy') → later dy ∼ later dy'

postulate quotient : ∀{X}{dx dx' : Delay X} → dx ∼ dx' → dx ≅ dx'


refl∼ : ∀{X}{dx : Delay X} → dx ∼ dx
refl∼ {dx = now x}    = ↓∼ now↓ now↓
refl∼ {dx = later dx} = later∼ (♯ refl∼)


dlaw1 : ∀{X}(dx : Delay X) → dbind now dx ∼ dx
dlaw1 (now x) = refl∼
dlaw1 (later dx) = later∼ (♯ dlaw1 (♭ dx))

--dlaw2 holds definitionally

dlaw3 : ∀{X Y Z}{f : X → Delay Y} {g : Y → Delay Z}(dx : Delay X) → 
        dbind (dbind g ∘ f) dx ∼ dbind g (dbind f dx)
dlaw3 {f = f}{g = g} (now x)   = refl∼
dlaw3 {f = f}{g = g} (later x) = later∼ (♯ dlaw3 (♭ x))

{-
-}

DelayM : Monad Sets
DelayM = record { 
  T    = Delay; 
  η    = now; 
  bind = dbind; 
  law1 = ext (quotient ∘ dlaw1); 
  law2 = refl; 
  law3 = ext (quotient ∘ dlaw3) }


help : ∀{X Y}(x : X) → Delay Y → Delay X
help x (now y)    = now x
help x (later dy) = later (♯ help x (♭ dy))

drest : ∀{X Y} → (X → Delay Y) → X → Delay X
drest f x = help x (f x) 

{-
dR1help : ∀{X Y}{f : X → Delay Y}(x : X)(dy : Delay Y) → f x ≅ dy → (dbind f) (help x dy) ∼ dy
dR1help x (now y) p    = {!!}
dR1help x (later dy) p = later∼ (♯ dR1help x (♭ dy) {!!})
-}

open Cat (Kl DelayM)

{-
dR1 : ∀{X Y}{f : X → Delay Y}(x : X) → (comp f (drest f)) x ∼ f x
dR1 {f = f} x with f x   | inspect f x
dR1 {f = f} x | now y    | [ eq ] = {!!}
dR1 {f = f} x | later dy | [ eq ] = later∼ {!!}
-}

DelayR : RestCat
DelayR = record { 
  cat  = Kl DelayM; 
  rest = drest; 
  R1   = {!!}; 
  R2   = {!!}; 
  R3   = {!!}; 
  R4   = {!!} }