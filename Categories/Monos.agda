
open import Categories

module Categories.Monos {i j}(X : Cat {i}{j}) where
open import Utilities

open Cat X

Mono : ∀{A B} → Hom A B → Set (i ⊔ j)
Mono f = ∀{C}{g h : Hom C _} → (comp f g ≅ comp f h) → g ≅ h

idMono : ∀{A} → Mono (iden {A})
idMono {g = g}{h} p = 
  proof
  g 
  ≅⟨ sym idl ⟩ 
  comp iden g 
  ≅⟨ p ⟩ 
  comp iden h 
  ≅⟨ idl ⟩ 
  h 
  ∎

compMono : ∀{A B C}{g : Hom B C}{f : Hom A B} → Mono g → Mono f → 
           Mono (comp g f)
compMono {g = g}{f} q p {_}{h1}{h2} r = p $ q $
  proof 
  comp g (comp f h1)
  ≅⟨ sym ass ⟩ 
  comp (comp g f) h1 
  ≅⟨ r ⟩ 
  comp (comp g f) h2 
  ≅⟨ ass ⟩ 
  comp g (comp f h2) 
  ∎
