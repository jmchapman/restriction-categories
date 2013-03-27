{-# OPTIONS --type-in-type #-}

module PartialDelay where

open import Coinduction
open import Categories
open import Monads
open import Functors
open import Kleisli
open import Sets
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Data.Product hiding (map) renaming (proj₁ to fst; proj₂ to snd)
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
  ↓∼ : ∀{dy dy' y} → dy ↓ y → dy' ↓ y → dy ∼ dy'
  later∼ : ∀{dy dy'} → ∞ (♭ dy ∼ ♭ dy') → later dy ∼ later dy'

postulate quotient : ∀{X}{dx dx' : Delay X} → dx ∼ dx' → dx ≅ dx'

refl∼ : ∀{X}{dx : Delay X} → dx ∼ dx
refl∼ {dx = now x}    = ↓∼ now↓ now↓
refl∼ {dx = later dx} = later∼ (♯ refl∼)

trans∼ : ∀{X}{dx dx' dx'' : Delay X} → dx ∼ dx' → dx' ∼ dx'' → dx ∼ dx''
trans∼ p q = {!!}

dlaw1 : ∀{X}(dx : Delay X) → dbind now dx ∼ dx
dlaw1 (now x) = refl∼
dlaw1 (later dx) = later∼ (♯ dlaw1 (♭ dx))

--dlaw2 holds definitionally

dlaw3 : ∀{X Y Z}{f : X → Delay Y} {g : Y → Delay Z}(dx : Delay X) → 
        dbind (dbind g ∘ f) dx ∼ dbind g (dbind f dx)
dlaw3 {f = f}{g = g} (now x)   = refl∼
dlaw3 {f = f}{g = g} (later x) = later∼ (♯ dlaw3 (♭ x))


DelayM : Monad Sets
DelayM = record { 
  T    = Delay; 
  η    = now; 
  bind = dbind; 
  law1 = ext (quotient ∘ dlaw1); 
  law2 = refl; 
  law3 = ext (quotient ∘ dlaw3) }


{-
help : ∀{X Y}(x : X) → Delay Y → Delay X
help x (now y)    = now x
help x (later dy) = later (♯ help x (♭ dy))

drest : ∀{X Y} → (X → Delay Y) → X → Delay X
drest f x = help x (f x) 
-}

str : ∀{X Y} → X × Delay Y → Delay (X × Y)
str (x , dy) = dbind (λ y → now (x , y)) dy

map = Fun.HMap (TFun DelayM)

drest : ∀{X Y} → (X → Delay Y) → X → Delay X
drest f x = map fst (str (x , f x))

{-
drest f x
= def
map fst (str (x , f x))
= def
dbind (now ∘ fst) (dbind (λ y → now (x , y)) (f x))
= law3
dbind (dbind (now ∘ fst) ∘ (λ x₁ → now (x , x₁))) (f x) ?
= computation
dbind now (f x) 
= law1
f x
-}

open Cat (Kl DelayM)

dR1 : ∀{X Y}{f : X → Delay Y}(x : X) → (dbind f ∘ (drest f)) x ∼ f x
dR1 {f = f} x = let open Monad DelayM in {! !}

{-
dR1 {f = f} x with f x   | inspect f x
dR1 {f = f} x | now y    | [ eq ] = {!!}
dR1 {f = f} x | later dy | [ eq ] = later∼ {!!}
-}

DelayR : RestCat
DelayR = record { 
  cat  = Kl DelayM; 
  rest = drest; 
  R1   = {!Monad.law3 DelayM!}; 
  R2   = {!!}; 
  R3   = {!!}; 
  R4   = {!!} }

