
module RestrictionExamples where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Function
open import Categories
open import Stable
open import RestrictionCat


-- Restriction operation in the partial map category

module Ex1 (X : Cat) (M : StableSys X) where

  open import PartialMaps X M
  open Cat X
  open StableSys X M

  restp : ∀{A B} → Span A B → Span A A
  restp mf = 
    let open Span mf
    in record { 
      A' = A'; 
      mhom = mhom; 
      fhom = mhom; 
      m∈ = m∈ }


-- Proofs of two lemmas regarding restriction

module Ex2 (X : RestCat) where

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
