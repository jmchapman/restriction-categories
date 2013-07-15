open import Categories
open import Level

module Categories.Isos {a b}(X : Cat {a}{b}) where
  open import Relation.Binary.HeterogeneousEquality
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Function

  open Cat X


  record Iso {A B : Obj} (f : Hom A B) : Set (a ⊔ b) where
    constructor _,,_,,_
    field inv  : Hom B A
          .rinv : comp f inv ≅ iden {B}
          .linv : comp inv f ≅ iden {A}

  idiso : ∀{A} → Iso (iden {A})
  idiso = iden ,, idl ,, idl

  .invuniq : ∀{A B}(f : Hom A B)(p q : Iso f) → Iso.inv p ≅ Iso.inv q
  invuniq f piso qiso =
    let open Iso piso renaming (inv to g; rinv to p; linv to p') 
        open Iso qiso renaming (inv to g'; rinv to q; linv to q') 
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


  open import Categories.Monos X

  .iso→mono : ∀{A B}{f : Hom A B} → Iso f → Mono f
  iso→mono {_}{_}{f} f'iso {_}{g}{h} q =
    let open Iso f'iso renaming (inv to f'; rinv to p; linv to p')
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

  .compisos : ∀{A B C}{f : Hom A B}{g : Hom B C} → Iso f → Iso g → 
             Iso (comp g f)
  compisos {_}{_}{_} {f} {g} piso qiso = 
    let open Iso piso renaming (inv to f'; rinv to p; linv to p') 
        open Iso qiso renaming (inv to g'; rinv to q; linv to q') 
    in 
    (comp f' g') ,, 
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
     ∎) ,, 
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
