open import Categories

module Categories.Monos (X : Cat) where
open import Utilities

open Cat X

Mono : ∀{A B} → Hom A B → Set
Mono f = ∀{C}{g h : Hom C _} → (comp f g ≅ comp f h) → g ≅ h

.idmono : ∀{A} → Mono (iden {A})
idmono {_}{_}{g}{h} p = 
  proof
  g 
  ≅⟨ sym idl ⟩ 
  comp iden g 
  ≅⟨ p ⟩ 
  comp iden h 
  ≅⟨ idl ⟩ 
  h 
  ∎

.compmonos : ∀{A B C}(f : Hom A B)(g : Hom B C) → Mono f → Mono g → 
            Mono (comp g f)
compmonos f g p q {D}{h1}{h2} r = p $ q $
  proof 
  comp g (comp f h1)
  ≅⟨ sym ass ⟩ 
  comp (comp g f) h1 
  ≅⟨ r ⟩ 
  comp (comp g f) h2 
  ≅⟨ ass ⟩ 
  comp g (comp f h2) 
  ∎
