open import Restriction.Cat

module Restriction.Totals (X : RestCat) where
  open import Utilities
  open import Categories
  open RestCat X
  open Lemmata X
  open Cat cat
  open import Categories.Monos
  open import Categories.Isos

  record Tot (A B : Obj) : Set where
    field hom : Hom A B 
          .tot : rest hom ≅ iden {A}

  open Tot

  .TotEq' : ∀{A B}(f g : Hom A B) → f ≅ g → {p : rest f ≅ iden}
            {q : rest g ≅ iden} → 
            _≅_ {_}{Tot A B} (record {hom = f; tot = p}) {Tot A B}(record {hom = g; tot = q})
  TotEq' g .g refl = refl

  .TotEq : ∀{A B}{f g : Tot A B} → hom f ≅ hom g → f ≅ g
  TotEq {A}{B}{f}{g} p = cong₂
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
    idl  = TotEq idl;
    idr  = TotEq idr;
    ass  = TotEq ass}

  .MonoTot : ∀{A B}(f : Tot A B) → Mono cat (hom f) → Mono Total f
  MonoTot f p q = TotEq (p (cong hom q))

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

    in gt  ,, TotEq p ,, TotEq q

  TotEqHom : ∀{A B}{f g : Tot A B} → f ≅ g → hom f ≅ hom g
  TotEqHom p = cong hom p

