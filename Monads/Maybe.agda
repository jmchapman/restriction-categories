{-# OPTIONS --type-in-type #-}
module Monads.Maybe where

open import Monads
open import Categories.Sets
open import Data.Maybe
open import Utilities

mbind : {X Y : Set} → (X → Maybe Y) → Maybe X → Maybe Y
mbind f (just x) = f x
mbind f nothing  = nothing

mlaw1 : ∀{A}(a : Maybe A) → mbind just a ≅ id a
mlaw1 (just a) = refl
mlaw1 nothing  = refl

mlaw3 : ∀{A B C}{f : A → Maybe B}{g : B → Maybe C}(a : Maybe A) → 
        mbind (mbind g ∘ f) a  ≅ (mbind g ∘ mbind f) a
mlaw3 (just a) = refl
mlaw3 nothing  = refl

MaybeMonad : Monad Sets
MaybeMonad = record {
  T    = Maybe;
  η    = just;
  bind = mbind;
  law1 = ext mlaw1;
  law2 = refl;
  law3 = ext mlaw3}
