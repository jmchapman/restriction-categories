{-# OPTIONS --type-in-type #-}

open import RestrictionCat

module RestrictionExample2 (X : RestCat) where

  open import Categories
  open import Relation.Binary.HeterogeneousEquality
  open import Equality
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Function
  open import Data.Product
  open RestCat X
  open Cat cat
  
  lemmaII : ∀{A B}{f : Hom A B} → comp (rest f) (rest f) ≅ rest f
  lemmaII {f = f} = 
    proof
    comp (rest f) (rest f) 
    ≅⟨ R3 ⟩ 
    rest (comp f (rest f))
    ≅⟨ cong rest R1 ⟩ 
    rest f
    ∎

  open Monos cat

  lemIII : ∀{A B}{f : Hom A B} → Mono f → rest f ≅ iden
  lemIII {f = f} p = p $
    proof
    comp f (rest f)
    ≅⟨ R1 ⟩ 
    f
    ≅⟨ sym idr ⟩ 
    comp f iden
    ∎
