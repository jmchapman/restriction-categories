{-# OPTIONS --type-in-type #-}
open import Categories
module Stable (X : Cat) where
  open import Relation.Binary.HeterogeneousEquality
  open ≅-Reasoning renaming (begin_ to proof_ ; _≅⟨_⟩_ to _≅[_]_)
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
    field ∈   : ∀{X Y}(f : Hom X Y) → Set
          mon : ∀{X Y}{f : Hom X Y} → ∈ f → Mono f
          iso : ∀{X Y}{f : Hom X Y} → Iso f → ∈ f 
          com : ∀{X Y Z}{f : Hom Z X}{g : Hom X Y} → ∈ f → ∈ g → ∈ (comp g f)
          pul : ∀{X Y Z}(f : Hom X Z){m : Hom Y Z} → ∈ m → 
                Σ (Pullback f m) λ p → ∈ (h (sq p))
  

  AllIsos : StableSys
  AllIsos = record { 
    ∈   = Iso; 
    mon = iso→mono; 
    iso = id; 
    com = compisos; 
    pul = λ f p → (iso→pullback p) , iden , idl , idl }


  module PartialCats (X : Cat)(M : StableSys) where

    open StableSys M

    record Span (A B : Obj) : Set where
      field A' : Obj
            mhom : Hom A' A
            fhom : Hom A' B
            m∈ : ∈ mhom

    open Span
    open Pullback
    open Square

    postulate cheat : ∀{A B}(mf m'f' : Span A B)
                      → (s : Hom (A' mf) (A' m'f')) → Iso s → comp (mhom m'f') s ≅ (mhom mf) 
                      → comp (fhom m'f') s ≅ (fhom mf) → mf ≅ m'f'

    Partials : Cat
    Partials = record {
                 Obj = Obj;
                 Hom = Span;
                 iden = λ {X} → record { 
                   A' = X; 
                   mhom = iden;
                   fhom = iden;
                   m∈ = iso (iden , idl , idl)};                
                 comp = λ {X}{Y}{Z} m'f' mf → 
                   let x = pul (fhom mf) (m∈ m'f')
                       y = sq (proj₁ x)
                   in record {
                     A' = W y; 
                     mhom = comp (mhom mf) (h y); 
                     fhom = comp (fhom m'f') (k y); 
                     m∈ = com (proj₂ x) (m∈ mf)};
                 idl = λ {X} {Y} {mf} → cheat 
                   _ 
                   _ 
                   (h (sq (proj₁ (pul (fhom mf)  (iso (iden , idl , idl)))))) 
                   (pullbackiso (trivialpul (fhom mf)) 
                                (proj₁ (pul (fhom mf) (iso ((iden , idl , idl)))))) 
                   refl
                   (scom (sq (proj₁ (pul (fhom mf)  (iso (iden , idl , idl))))));
                 idr = λ {X} {Y} {mf} → cheat 
                   _ 
                   _ 
                   (k (sq (proj₁ (pul iden (m∈ mf))))) 
                   (pullbackiso (trivialpul2 (mhom mf)) (proj₁ (pul iden (m∈ mf)))) 
                   (sym (scom (sq (proj₁ (pul iden (m∈ mf)))))) 
                   refl;
                 ass = {!!} }

