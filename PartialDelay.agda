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

data _∼_ {X : Set} : Delay X → Delay X → Set where
  now∼ : ∀{x : X} → now x ∼ now x
  later∼ : ∀{dx dx' : ∞ (Delay X)} → ∞ (♭ dx ∼ ♭ dx') → later dx ∼ later dx'

refl∼ : ∀{X}{dx : Delay X} → dx ∼ dx
refl∼ {dx = now x}    = now∼
refl∼ {dx = later dx} = later∼ (♯ refl∼)

dbind : ∀{X Y} → (X → Delay Y) → Delay X → Delay Y
dbind f (now x)   = f x
dbind f (later x) = later (♯ dbind f (♭ x))

dlaw1 : ∀{X}(dx : Delay X) → dbind now dx ∼ dx
dlaw1 (now x)   = now∼
dlaw1 (later x) = later∼ (♯ dlaw1 (♭ x))

--dlaw2 holds definitionally

dlaw3 : ∀{X Y Z}{f : X → Delay Y} {g : Y → Delay Z}(dx : Delay X) → 
        dbind (dbind g ∘ f) dx ∼ dbind g (dbind f dx)
dlaw3 {f = f}{g = g} (now x)   = refl∼
dlaw3 {f = f}{g = g} (later x) = later∼ (♯ dlaw3 (♭ x))

postulate quotient : ∀{X}{dx dx' : Delay X} → dx ∼ dx' → dx ≅ dx'

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

dR1help : ∀{X Y}{f : X → Delay Y}(x : X)(dy : Delay Y) → f x ≅ dy → (dbind f) (help x dy) ∼ dy
dR1help x (now y) p    = {!!}
dR1help x (later dy) p = later∼ (♯ dR1help x (♭ dy) {!!})

open Cat (Kl DelayM)

dR1 : ∀{X Y}{f : X → Delay Y}(x : X) → (comp f (drest f)) x ∼ f x
dR1 {f = f} x with f x   | inspect f x
dR1 {f = f} x | now y    | [ eq ] = {!!}
dR1 {f = f} x | later dy | [ eq ] = {!  !}

DelayR : RestCat
DelayR = record { 
  cat  = Kl DelayM; 
  rest = drest; 
  R1   = {!!}; 
  R2   = {!!}; 
  R3   = {!!}; 
  R4   = {!!} }