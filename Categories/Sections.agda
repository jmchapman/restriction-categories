open import Categories

module Categories.Sections {a b}(X : Cat {a}{b}) where
  open import Relation.Binary.HeterogeneousEquality
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Function
  open import Data.Product

  open Cat X
  open import Categories.Monos X

  Sec : ∀{A B} → Hom A B → Set b
  Sec {A}{B} s = Σ (Hom B A) λ r → comp r s ≅ iden {A}

  .smon : ∀{A B}(s : Hom A B) → Sec s → Mono s
  smon s (r , q) {_}{g}{h} p = 
    proof
    g
    ≅⟨ sym idl ⟩
    comp iden g
    ≅⟨ cong (λ y → comp y g) (sym q) ⟩
    comp (comp r s) g
    ≅⟨ ass ⟩
    comp r (comp s g)
    ≅⟨ cong (comp r) p ⟩
    comp r (comp s h)
    ≅⟨ sym ass ⟩
    comp (comp r s) h
    ≅⟨ cong (λ y → comp y h) q ⟩
    comp iden h
    ≅⟨ idl ⟩
    h
    ∎
