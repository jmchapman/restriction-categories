{-# OPTIONS --type-in-type #-}

module Restriction.Maybe where
open import Utilities
open import Categories
open import Data.Maybe
open import Restriction.Cat

open import Monads
open import Monads.Kleisli
open import Categories.Sets
open import Monads.Maybe

rest : ∀{X Y} → (X → Maybe Y) → X → Maybe X
rest f x with f x
... | nothing = nothing
... | just y  = just x

PartRestCat : RestCat
PartRestCat = record { 
  cat  = Kl MaybeMonad; 
  rest = rest;
  R1   = λ{_}{_}{f} → ext (mR1 f); 
  R2   = λ{_}{_}{_}{f}{g} → ext (mR2 f g);
  R3   = λ{_}{_}{_}{f}{g} → ext (mR3 f g);
  R4   = λ{_}{_}{_}{f}{g} → ext (mR4 f g)}
  where
  mR1 : {A B : Set}(f : A → Maybe B)(x : A) → mbind f (rest f x) ≅ f x
  mR1 f x with f x  | inspect f x
  mR1 f x | just y  | [ eq ] = eq
  mR1 f x | nothing | [ eq ] = refl

  -- can't use rewrite with het. eq. unless we redefine a pragma somewhere
  mR2 : {A B C : Set} (f : A → Maybe B)(g : A → Maybe C)(x : A) → 
    mbind (rest f) (rest g x) ≅ mbind (rest g) (rest f x)
  mR2 f g x with f x | inspect f x | g x | inspect g x
  mR2 f g x | just y  | [ eq ] | just z  | [ eq₁ ] with f x | eq | g x | eq₁
  ... | ._ | refl | ._ | refl = refl
  mR2 f g x | just y  | [ eq ] | nothing | [ eq₁ ]  with f x | eq | g x | eq₁
  ... | ._ | refl | ._ | refl = refl
  mR2 f g x | nothing | [ eq ] | just z  | [ eq₁ ]  with f x | eq | g x | eq₁
  ... | ._ | refl | ._ | refl = refl
  mR2 f g x | nothing | [ eq ] | nothing | [ eq₁ ] = refl

  mR3 : {A B C : Set}(f : A → Maybe B)(g : A → Maybe C)(x : A) →
    mbind (rest g) (rest f x) ≅ rest (λ x' → mbind g (rest f x')) x
  mR3 {A} f g x with f x 
  mR3 f g x | just y with g x
  mR3 f g x | just y | just z = refl
  mR3 f g x | just y | nothing = refl
  mR3 f g x | nothing = refl

  mR4 : {A B C : Set}(f : A → Maybe B)(g : B → Maybe C)(x : A) →
        mbind (rest g) (f x) ≅ mbind f (rest (λ x' → mbind g (f x')) x)
  mR4 f g x with f x | inspect f x
  mR4 f g x | just x' | [ eq ] with g x'
  mR4 f g x | just x' | [ eq ] | just x'' = sym eq
  mR4 f g x | just x' | [ eq ] | nothing = refl
  mR4 f g x | nothing | [ eq ] = refl
