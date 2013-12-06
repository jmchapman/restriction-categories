open import Restriction.Cat

module Restriction.Totals (X : RestCat) where

  open import Categories
  open import Relation.Binary.HeterogeneousEquality
  open import Utilities
  open ≅-Reasoning renaming (begin_ to proof_)
  open RestCat X
  open Lemmata X
  open Cat cat
  open import Categories.Monos
  open import Categories.Isos

  record Tot (A B : Obj) : Set where
    field hom : Hom A B 
          .tot : rest hom ≅ iden {A}

  open Tot

  .TotEq : ∀{A B}(f g : Tot A B) → hom f ≅ hom g → f ≅ g
  TotEq {A}{B} f g p = cong₂
    {_}
    {_}
    {_}
    {Hom A B}
    {λ hom → rest hom ≅ iden {A}}
    {λ _ _ → Tot A B}
    {hom f}
    {hom g}
    {tot f}
    {tot g}    
    (λ x y → record { hom = x; tot = y }) 
    p 
    (fixtypes'' refl)

  identot : ∀{A} → Tot A A
  identot = record { hom = iden; tot = lemiii (idmono cat) } 

  comptot : ∀{A B C}(g : Tot B C)(f : Tot A B) → Tot A C
  comptot g f = record { 
    hom = comp (hom g) (hom f); 
    tot = 
      proof
      rest (comp (hom g) (hom f)) 
      ≅⟨ lemiv ⟩ 
      rest (comp (rest (hom g)) (hom f)) 
      ≅⟨ cong (λ h → rest (comp h (hom f))) (tot g) ⟩ 
      rest (comp iden (hom f))
      ≅⟨ cong rest idl ⟩ 
      rest (hom f)
      ≅⟨ tot f ⟩ 
      iden
      ∎}

  Total : Cat
  Total = record {
    Obj  = Obj; 
    Hom  = Tot;
    iden = identot;
    comp = comptot;
    idl  = λ{_}{_}{f} → TotEq (comptot identot f) f idl;
    idr  = λ{_}{_}{f} → TotEq (comptot f identot) f idr;
    ass  = λ{_}{_}{_}{_}{f}{g}{h} → 
      TotEq (comptot (comptot f g) h) (comptot f (comptot g h)) ass}

  .MonoTot : ∀{A B}(f : Tot A B) → Mono cat (hom f) → Mono Total f
  MonoTot f p {C}{g}{h} q = TotEq g h (p (cong hom q))

  IsoTot : ∀{A B}(f : Tot A B) → Iso cat (hom f) → Iso Total f
  IsoTot f fiso = 
    let open Iso cat fiso renaming (inv to g; rinv to p; linv to q) 
        open Tot f renaming (hom to fhom)
        gt = record { 
          hom = g; 
          tot = iso→mono cat (fhom ,, q ,, p) 
                         (proof
                          comp g (rest g)
                          ≅⟨ R1 ⟩
                          g
                          ≅⟨ sym idr ⟩
                          comp g iden
                          ∎) }

    in gt  ,, 
     TotEq (comptot f gt) identot p ,,
     TotEq (comptot gt f) identot q

  TotEqHom : ∀{A B}{f g : Tot A B} → f ≅ g → hom f ≅ hom g
  TotEqHom p = cong hom p
