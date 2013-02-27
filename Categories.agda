{-# OPTIONS --type-in-type #-}
module Categories where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Data.Product

record Cat : Set where
  field Obj  : Set
        Hom  : Obj → Obj → Set
        iden : ∀{X} → Hom X X
        comp : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → comp iden f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → comp f iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
               comp (comp f g) h ≅ comp f (comp g h)

module Monos (X : Cat) where
  open Cat X

  Mono : ∀{A B} → Hom A B → Set
  Mono f = ∀{C}{g h : Hom C _} → comp f g ≅ comp f h → g ≅ h

  idmono : ∀{A} → Mono (iden {A})
  idmono {A}{C}{g}{h} p = 
    proof
    g 
    ≅⟨ sym idl ⟩ 
    comp iden g 
    ≅⟨ p ⟩ 
    comp iden h 
    ≅⟨ idl ⟩ 
    h 
    ∎

module Isos (X : Cat) where
  open Cat X

  Iso : ∀{A B} → Hom A B → Set
  Iso {A}{B} f = Σ (Hom B A) (λ g → comp f g ≅ iden {B} × comp g f ≅ iden {A})


  invuniq : ∀{A B}(f : Hom A B)(p q : Iso f) → proj₁ p ≅ proj₁ q
  invuniq f (g , p , p') (g' , q , q') = 
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


_Op : Cat → Cat
C Op = record {
  Obj  = Obj; 
  Hom  = λ X Y → Hom Y X;
  iden = iden;
  comp = λ f g → comp g f; 
  idl  = idr;
  idr  = idl;
  ass  = sym ass}
  where open Cat C
