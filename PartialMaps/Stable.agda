{-# OPTIONS --type-in-type #-}
open import Categories
module PartialMaps.Stable (X : Cat) where
  open import Relation.Binary.HeterogeneousEquality
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Data.Product
  open import Function
  open Cat X
  open import Categories.Pullbacks X
  open import Categories.Monos X
  open import Categories.Isos X
  open import Categories.Pullbacks.PullbacksLemmas X

  record StableSys : Set where
    open Pullback
    open Square
    field ∈   : ∀{X Y}(f : Hom X Y) → Set
          .mon : ∀{X Y}{f : Hom X Y} → ∈ f → Mono f
          iso : ∀{X Y}{f : Hom X Y} → Iso f → ∈ f 
          com : ∀{X Y Z}{f : Hom Z X}{g : Hom X Y} → ∈ f → ∈ g → ∈ (comp g f)
          pul : ∀{X Y Z}(f : Hom X Z){m : Hom Y Z} → ∈ m → 
                Σ (Pullback f m) λ p → ∈ (h (sq p))
  
{-
  AllIsos : StableSys
  AllIsos = record { 
    ∈   = Iso; 
    mon = iso→mono; 
    iso = id; 
    com = compisos; 
    pul = λ f p → (iso→pullback p) ,, idiso }
-}

