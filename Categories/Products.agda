
open import Categories

module Categories.Products (X : Cat) where
open import Utilities

open Cat X

record Prod (A B : Obj) : Set where
  field W : Obj
        p₁ : Hom W A
        p₂ : Hom W B
        ⟨_,_⟩ : ∀{C} → Hom C A → Hom C B → Hom C W
        .tr1 : ∀{C}{f : Hom C A}{g : Hom C B} → comp p₁ ⟨ f , g ⟩ ≅ f
        .tr2 : ∀{C}{f : Hom C A}{g : Hom C B} → comp p₂ ⟨ f , g ⟩ ≅ g
        .uniq : ∀{C}{f : Hom C A}{g : Hom C B} → (u : Hom C W) → 
               comp p₁ u ≅ f → comp p₂ u ≅ g → u ≅ ⟨ f , g ⟩ 

record TermObj : Set where
  field one : Obj
        ! : ∀{A} → Hom A one
        .uniq : ∀{A}(u : Hom A one) → u ≅ ! {A}
        
