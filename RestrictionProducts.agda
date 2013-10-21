
open import RestrictionCat

module RestrictionProducts (X : RestCat) where

open import Function
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open import Data.Product hiding (map)
open ≅-Reasoning renaming (begin_ to proof_)
open import Level
open import Categories
open import Totals X
open RestCat X
open Cat cat
open Tot

record RestProd (A B : Obj) : Set where
  field W : Obj
        p₁ : Tot W A
        p₂ : Tot W B
        ⟨_,_⟩ : ∀{C} → Hom C A → Hom C B → Hom C W
        .tr1 : ∀{C}{f : Hom C A}{g : Hom C B} → 
               comp (hom p₁) ⟨ f , g ⟩ ≅ comp f (rest g)
        .tr2 : ∀{C}{f : Hom C A}{g : Hom C B} → 
               comp (hom p₂) ⟨ f , g ⟩ ≅ comp g (rest f)
        .uniq : ∀{C}{f : Hom C A}{g : Hom C B} → (u : Hom C W) → 
                comp (hom p₁) u ≅ comp f (rest g) → 
                comp (hom p₂) u ≅ comp g (rest f)→ u ≅ ⟨ f , g ⟩ 
