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

-- do these little proofs need to be so complicated?
mR1 : {A B : Set}(f : A → Maybe B)(x : A)(y : Maybe B) → f x ≡ y  →
  mbind f (mif y (just x) nothing) ≡ y
mR1 f x (just x₁) p with f x 
mR1 f x (just x₂) refl | just .x₂ = refl
mR1 f x (just x₁) () | nothing
mR1 f x nothing p = refl

mR2 : {A B C : Set} (f : A → Maybe B)(g : A → Maybe C)(x : A) → 
      (m : Maybe B)(m' : Maybe C) → f x ≡ m → g x ≡ m' →
 mbind (λ a → mif (f a) (just a) nothing)
   (mif m' (just x) nothing)
 ≡
 mbind (λ a → mif (g a) (just a) nothing)
   (mif m (just x) nothing)
mR2 f g x (just x₁) (just x₂) p q with f x | g x
mR2 f g x (just x₂) (just x₃) p refl | just x₁ | .(just x₃) = refl
mR2 f g x (just x₂) (just x₃) () q | nothing | just x₁
mR2 f g x (just x₁) (just x₂) p q | nothing | nothing = refl
mR2 f g x (just x₁) nothing p q with f x | g x
mR2 f g x (just x₃) nothing p () | just x₁ | just x₂
mR2 f g x (just x₂) nothing p q | just x₁ | nothing = refl
mR2 f g x (just x₂) nothing p () | nothing | just x₁
mR2 f g x (just x₁) nothing p q | nothing | nothing = refl
mR2 f g x nothing (just x₁) p q with f x
mR2 f g x nothing (just x₂) () q | just x₁
mR2 f g x nothing (just x₁) p q | nothing = refl
mR2 f g x nothing nothing p q     = refl

mR3 : {A B C : Set}(f : A → Maybe B)(g : A → Maybe C)(x : A) →
      (m : Maybe B)(m' : Maybe C) → f x ≡ m → g x ≡ m' → 
      mif (mbind g (mif m (just x) nothing)) (just x) nothing
      ≡
     mbind (λ a → mif (f a) (just a) nothing)
      (mif m' (just x) nothing)
mR3 f g x (just x₁) (just x₂) p q with f x | g x
mR3 f g x (just x₃) (just x₄) p q | just x₁ | just x₂ = refl
mR3 f g x (just x₂) (just x₃) p () | just x₁ | nothing
mR3 f g x (just x₂) (just x₃) () q | nothing | just x₁
mR3 f g x (just x₁) (just x₂) p q | nothing | nothing = refl
mR3 f g x (just x₁) nothing p q with g x 
mR3 f g x (just x₂) nothing p () | just x₁
mR3 f g x (just x₁) nothing p q | nothing = refl
mR3 f g x nothing (just x₁) p q with f x 
mR3 f g x nothing (just x₂) () q | just x₁
mR3 f g x nothing (just x₁) p q | nothing = refl
mR3 f g x nothing nothing p q = refl

mR4 : {A B C : Set}(f : A → Maybe B)(g : B → Maybe C)(x : A) →
      (m : Maybe B) → f x ≡ m → 
      mbind (λ a → mif (g a) (just a) nothing) m
      ≡
      mbind f (mif (mbind g m) (just x) nothing)
mR4 f g x (just x') p with g x' 
mR4 f g x₁ (just x') p | just x = sym p
mR4 f g x (just x') p | nothing = refl
mR4 f g x nothing p = refl

PartRestCat : RestCat
PartRestCat = record { 
  cat  = PartialCat; 
  rest = λ f a → mif (f a) (just a) nothing; 
  R1   = λ {A} {B} {f} → ext (λ x → mR1 f x (f x) refl); 
  R2   = λ {A} {B} {C} {f} {g} → ext (λ x → mR2 f g x (f x) (g x) refl refl);
  R3   = λ {A} {B} {C} {f} {g} → ext (λ x → mR3 f g x (f x) (g x) refl refl);
  R4   = λ {A} {B} {C} {f} {g} → ext (λ x → mR4 f g x (f x) refl)}