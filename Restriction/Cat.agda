{-# OPTIONS --type-in-type #-}
module Restriction.Cat where

open import Utilities
open import Categories

record RestCat : Set where
  field cat  : Cat
  open  Cat cat
  field rest : ∀{A B} → Hom A B → Hom A A
        R1   : ∀{A B}{f : Hom A B} → comp f (rest f) ≅ f 
        R2   : ∀{A B C}{f : Hom A B}{g : Hom A C} →
               comp (rest f) (rest g) ≅ comp (rest g) (rest f)
        R3   : ∀{A B C}{f : Hom A B}{g : Hom A C} →
               comp (rest g) (rest f) ≅ rest (comp g (rest f))
        R4   : ∀{A B C}{f : Hom A B}{g : Hom B C} →
               comp (rest g) f ≅ comp f (rest (comp g f))

module Lemmata (X : RestCat) where

  open RestCat X
  open Cat cat
  open import Categories.Monos cat
  
  lemii : ∀{A B}{f : Hom A B} → comp (rest f) (rest f) ≅ rest f
  lemii {f = f} = 
    proof
    comp (rest f) (rest f) 
    ≅⟨ R3 ⟩ 
    rest (comp f (rest f))
    ≅⟨ cong rest R1 ⟩ 
    rest f
    ∎

  lemiii : ∀{A B}{f : Hom A B} → Mono f → rest f ≅ iden
  lemiii {f = f} p = p $
    proof
    comp f (rest f)
    ≅⟨ R1 ⟩ 
    f
    ≅⟨ sym idr ⟩ 
    comp f iden
    ∎

  lemi : ∀{A B}{f : Hom A B} → rest (rest f) ≅ rest f
  lemi {f = f} = 
    proof
    rest (rest f)
    ≅⟨ cong rest (sym idl) ⟩ 
    rest (comp iden (rest f))
    ≅⟨ sym R3 ⟩ 
    comp (rest iden) (rest f)
    ≅⟨ cong (λ g → comp g (rest f)) (lemiii idMono) ⟩ 
    comp iden (rest f)
    ≅⟨ idl ⟩ 
    rest f
    ∎

  lemiv : ∀{A B C}{f : Hom A B}{g : Hom B C} → 
          rest (comp g f) ≅ rest (comp (rest g) f)
  lemiv {f = f}{g = g} = 
    proof
    rest (comp g f) 
    ≅⟨ cong (λ f' → rest (comp g f')) (sym R1) ⟩ 
    rest (comp g (comp f (rest f))) 
    ≅⟨ cong rest (sym ass) ⟩ 
    rest (comp (comp g f) (rest f)) 
    ≅⟨ sym R3 ⟩ 
    comp (rest (comp g f)) (rest f) 
    ≅⟨ R2 ⟩ 
    comp (rest f) (rest (comp g f)) 
    ≅⟨ R3 ⟩ 
    rest (comp f (rest (comp g f))) 
    ≅⟨ cong rest (sym R4) ⟩ 
    rest (comp (rest g) f) 
    ∎

{-
  _≤_ : ∀{A B} → Hom A B → Hom A B → Set
  f ≤ g = comp g (rest f) ≅ f

  -- antisymmetry
  .ex1 : ∀{A B}(f g : Hom A B) → f ≤ g → g ≤ f → f ≅ g
  ex1 f g p q = 
    proof 
    f 
    ≅⟨ sym p ⟩ 
    comp g (rest f)
    ≅⟨ cong (λ g' → comp g' (rest f)) (sym q) ⟩ 
    comp (comp f (rest g)) (rest f)
    ≅⟨ ass ⟩ 
    comp f (comp (rest g) (rest f))
    ≅⟨ cong (comp f) (sym R2) ⟩ 
    comp f (comp (rest f) (rest g))
    ≅⟨ sym ass ⟩ 
    comp (comp f (rest f)) (rest g)
    ≅⟨ cong (λ f' → comp f' (rest g)) R1 ⟩ 
    comp f (rest g)
    ≅⟨ q ⟩ 
    g 
    ∎



Trivial : Cat → RestCat
Trivial C = record { 
  cat  = C; 
  rest = λ _ → iden; 
  R1   = idr; 
  R2   = refl; --proof comp iden iden ∎;
  R3   = idr; 
  R4   = λ {_ _ _ f} →
   proof 
   comp iden f 
   ≅⟨ idl ⟩ 
   f 
   ≅⟨ sym idr ⟩ 
   comp f iden 
   ∎}
  where open Cat C
-}
