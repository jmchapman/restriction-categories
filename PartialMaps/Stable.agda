{-# OPTIONS --type-in-type #-}
open import Categories

module PartialMaps.Stable (X : Cat) where

open import Utilities
open Cat X
open import Categories.Pullbacks X
open import Categories.Monos X
open import Categories.Isos X
open Pullback
open Square

record StableSys : Set where
  field ∈sys     : ∀{X Y}(f : Hom X Y) → Set
        mono∈sys : ∀{X Y}{f : Hom X Y} → ∈sys f → Mono f
        iso∈sys  : ∀{X Y}{f : Hom X Y} → Iso f → ∈sys f 
        comp∈sys : ∀{X Y Z}{f : Hom Z X}{g : Hom X Y} → ∈sys f → ∈sys g → ∈sys (comp g f)
        pul∈sys  : ∀{X Y Z}(f : Hom X Z){m : Hom Y Z} → ∈sys m → 
                   Σ (Pullback f m) λ p → ∈sys (h (sq p))
  

