{-# OPTIONS --type-in-type #-}

module PartialMaybe where
open import Relation.Binary.PropositionalEquality
open import Function
open import Categories
open import Data.Maybe
open import RestrictionCat

open import Monads
open import Kleisli
open import Sets
open import MaybeMonad

PartialCat : Cat
PartialCat = Kl MaybeMonad

mif : ∀{X Y} → Maybe X → Y → Y → Y
mif (just x) l r = l
mif nothing  l r = r

rest : ∀{X Y} → (X → Maybe Y) → X → Maybe X
rest f x with f x
... | nothing = nothing
... | just y  = just x

-- do these little proofs need to be so complicated?
mR1 : {A B : Set}(f : A → Maybe B)(x : A) →
  mbind f (rest f x) ≡ f x
mR1 f x with f x  | inspect f x
mR1 f x | just y  | [ eq ] = eq
mR1 f x | nothing | [ eq ] = refl

mR2 : {A B C : Set} (f : A → Maybe B)(g : A → Maybe C)(x : A) → 
 mbind (rest f) (rest g x)
 ≡
 mbind (rest g) (rest f x)
mR2 f g x with f x | inspect f x | g x | inspect g x
mR2 f g x | just x₁ | [ eq ] | just x₂ | [ eq₁ ] rewrite eq | eq₁ = refl
mR2 f g x | just x₁ | [ eq ] | nothing | [ eq₁ ] rewrite eq₁ = refl
mR2 f g x | nothing | [ eq ] | just x₁ | [ eq₁ ] rewrite eq = refl
mR2 f g x | nothing | [ eq ] | nothing | [ eq₁ ] = refl

mR3 : {A B C : Set}(f : A → Maybe B)(g : A → Maybe C)(x : A) →
  mbind (rest g)
        (rest f x)
  ≡
  rest (λ x' → mbind g (rest f x')) x
mR3 {A} f g x with f x 
mR3 f g x | just y with g x
mR3 f g x | just y | just z = refl
mR3 f g x | just y | nothing = refl
mR3 f g x | nothing = refl

mR4 : {A B C : Set}(f : A → Maybe B)(g : B → Maybe C)(x : A) →
      mbind (rest g) (f x)
      ≡
      mbind f (rest (λ x' → mbind g (f x')) x)
mR4 f g x with f x | inspect f x
mR4 f g x | just x' | [ eq ] with g x'
mR4 f g x | just x' | [ eq ] | just x'' = sym eq
mR4 f g x | just x' | [ eq ] | nothing = refl
mR4 f g x | nothing | [ eq ] = refl

PartRestCat : RestCat
PartRestCat = record { 
  cat  = PartialCat; 
  rest = rest;
  R1   = λ{A}{B}{f} → ext (mR1 f); 
  R2   = λ{A}{B}{C}{f}{g} → ext (mR2 f g);
  R3   = λ{A}{B}{C}{f}{g} → ext (mR3 f g);
  R4   = λ{A}{B}{C}{f}{g} → ext (mR4 f g)}