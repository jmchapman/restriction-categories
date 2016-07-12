
open import Restriction.Cat

module Restriction.Products (X : RestCat) where

open import Utilities
open import Categories
open import Restriction.Totals X
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
