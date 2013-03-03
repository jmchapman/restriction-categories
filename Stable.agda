{-# OPTIONS --type-in-type #-}
open import Categories
module Stable (X : Cat) where
  open import Relation.Binary.HeterogeneousEquality
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Data.Product
  open import Function
  open Cat X
  open import Pullbacks X
  open Monos X
  open Isos X
  open import PullbacksLemmas X

  record StableSys : Set where
    open Pullback
    open Square
    field ∈   : ∀{X Y} → (f : Hom X Y) → Set
          mon : ∀{X Y}(f : Hom X Y) → ∈ f → Mono f
          iso : ∀{X Y}(f : Hom X Y) → Iso f → ∈ f 
          com : ∀{X Y Z}(f : Hom Z X)(g : Hom X Y) → ∈ f → ∈ g → ∈ (comp g f)
          pul : ∀{X Y Z}(f : Hom X Z)(m : Hom Y Z) → ∈ m → Σ (Pullback f m) λ p → ∈ (h (sq p))
  

  AllIsos : StableSys
  AllIsos = record { 
    ∈   = λ f → Iso f; 
    mon = iso→mono; 
    iso = λ f p → p; 
    com = compisos; 
    pul = λ f g p → (iso→pullback p) , iden , idl , idl }