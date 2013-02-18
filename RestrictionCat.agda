{-# OPTIONS --type-in-type #-}
module RestrictionCat where

open import Categories
open import Relation.Binary.HeterogeneousEquality
open import Equality
open ≅-Reasoning renaming (begin_ to proof_)
open import Function
open import Data.Product

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
               comp (rest g) f ≅ comp  f (rest (comp g f))


module Lemmata (X : RestCat) where
  open RestCat X
  open Cat cat
  open Monos cat
  
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
  lemiii {f = f} p = p (
    proof
    comp f (rest f)
    ≅⟨ R1 ⟩ 
    f
    ≅⟨ sym idr ⟩ 
    comp f iden
    ∎)

  lemi : ∀{A B}{f : Hom A B} → rest (rest f) ≅ rest f
  lemi {f = f} = 
    proof
    rest (rest f)
    ≅⟨ cong rest (sym idl) ⟩ 
    rest (comp iden (rest f))
    ≅⟨ sym R3 ⟩ 
    comp (rest iden) (rest f)
    ≅⟨ cong (λ g → comp g (rest f)) (lemiii idmono) ⟩ 
    comp iden (rest f)
    ≅⟨ idl ⟩ 
    rest f
    ∎

  lemiv : ∀{A B C}{f : Hom A B}{g : Hom B C} → 
          rest (comp g f) ≅ rest (comp (rest g) f)
  lemiv {f = f}{g = g} = 
    proof
    rest (comp g f) 
    ≅⟨ cong (rest ∘ comp g) (sym R1) ⟩ 
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

Trivial : Cat → RestCat
Trivial C = record { 
  cat  = C; 
  rest = λ _ → iden; 
  R1   = idr; 
  R2   = trans idr (sym idl); 
  R3   = idr; 
  R4   = trans idl (sym idr)} 
  where open Cat C

module Totals (X : RestCat) where
  open RestCat X
  open Lemmata X
  open Cat cat
  open Monos cat

  record Tot (A B : Obj) : Set where
    field hom : Hom A B 
          tot : rest hom ≅ iden {A}

  open Tot

  TotEq : ∀{A B}{f g : Tot A B} → hom f ≅ hom g → f ≅ g
  TotEq {A}{B}{f}{g} p = cong₂
    {_}
    {_}
    {_}
    {Hom A B}
    {λ hom → rest hom ≅ iden {A}}
    {λ _ _ → Tot A B}
    (λ x y → record { hom = x; tot = y }) p 
    (fixtypes (cong rest p) refl)

  Totals : Cat
  Totals = record {
    Obj  = Obj; 
    Hom  = Tot;
    iden = record { hom = iden; tot = lemiii idmono };
    comp = λ g f → record { 
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
        ∎
     };
    idl  = TotEq idl;
    idr  = TotEq idr;
    ass  = TotEq ass}

{-  
  TotalsR : RestCat
  TotalsR = record { 
    cat  = Totals; 
    rest = λ _ → record {hom = iden; 
                         tot = Lemmata.lemiii X (Monos.idmono cat)};
    R1   = TotEq idr;
    R2   = TotEq refl;
    R3   = TotEq idr;
    R4   = TotEq (trans idl (sym idr))}
-}

  TotalsR : RestCat
  TotalsR = record { 
    cat  = Totals; 
    rest = λ f → record { 
      hom = rest (hom f); 
      tot = 
        proof
        rest (rest (hom f))
        ≅⟨ lemi ⟩ 
        rest (hom f)
        ≅⟨ tot f ⟩ 
        iden
        ∎};
    R1   = TotEq R1;
    R2   = TotEq R2;
    R3   = TotEq R3;
    R4   = TotEq R4}