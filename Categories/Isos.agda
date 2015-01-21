{-# OPTIONS --type-in-type #-}
open import Categories

module Categories.Isos (X : Cat) where

open import Utilities
open Cat X
open import Categories.Monos X

record Iso {A B : Obj}(f : Hom A B) : Set where
  constructor iso
  field inv  : Hom B A
        rinv : comp f inv ≅ iden {B}
        linv : comp inv f ≅ iden {A}

record _∼_ (A B : Obj) : Set where
  field f    : Hom A B
        g    : Hom B A 
        rinv : comp f g ≅ iden {B}
        linv : comp g f ≅ iden {A}

idIso : ∀{A} → Iso (iden {A})
idIso = iso iden idl idl

invUniq : ∀{A B}{f : Hom A B}(p q : Iso f) → Iso.inv p ≅ Iso.inv q
invUniq {f = f} r s =
  let open Iso r renaming (inv to g; rinv to p; linv to p')
      open Iso s renaming (inv to g'; rinv to q; linv to q')
  in
    proof 
    g 
    ≅⟨ sym idr ⟩ 
    comp g iden
    ≅⟨ cong (comp g) (sym q) ⟩ 
    comp g (comp f g')
    ≅⟨ sym ass ⟩ 
    comp (comp g f) g'
    ≅⟨ cong (λ h → comp h g') p' ⟩     
    comp iden g'
    ≅⟨ idl ⟩     
    g'
    ∎

isoIsMono : ∀{A B}{f : Hom A B} → Iso f → Mono f
isoIsMono {f = f} r {_}{g}{h} q =
  let open Iso r renaming (inv to f'; rinv to p; linv to p')
  in
    proof 
    g 
    ≅⟨ sym idl ⟩ 
    comp iden g 
    ≅⟨ cong (λ h → comp h g) (sym p') ⟩ 
    comp (comp f' f) g 
    ≅⟨ ass ⟩ 
    comp f' (comp f g) 
    ≅⟨ cong (comp f') q ⟩ 
    comp f' (comp f h) 
    ≅⟨ sym ass ⟩ 
    comp (comp f' f) h 
    ≅⟨ cong (λ g → comp g h) p' ⟩ 
    comp iden h 
    ≅⟨ idl ⟩ 
    h 
    ∎

compIso : ∀{A B C}{g : Hom B C}{f : Hom A B} → Iso g → Iso f → 
          Iso (comp g f)
compIso {g = g}{f} (iso g' q q') (iso f' p p') = 
  iso (comp f' g')
      (proof 
       comp (comp g f) (comp f' g') 
       ≅⟨ ass ⟩ 
       comp g (comp f (comp f' g')) 
       ≅⟨ cong (comp g) (sym ass) ⟩ 
       comp g (comp (comp f f') g') 
       ≅⟨ cong (λ h → comp g (comp h g')) p ⟩ 
       comp g (comp iden g') 
       ≅⟨ cong (comp g) idl ⟩ 
       comp g g' 
       ≅⟨ q ⟩ 
       iden 
       ∎)
      (proof 
       comp (comp f' g') (comp g f) 
       ≅⟨ ass ⟩ 
       comp f' (comp g' (comp g f)) 
       ≅⟨ cong (comp f') (sym ass) ⟩ 
       comp f' (comp (comp g' g) f) 
       ≅⟨ cong (λ h → comp f' (comp h f)) q' ⟩ 
       comp f' (comp iden f) 
       ≅⟨ cong (comp f') idl ⟩ 
       comp f' f 
       ≅⟨ p' ⟩ 
       iden 
       ∎)
