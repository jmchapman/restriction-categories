{-# OPTIONS --type-in-type #-}
module Categories where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_ ; _≅⟨_⟩_ to _≅[_]_)
open import Data.Product
open import Function

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
    ≅[ sym idl ] 
    comp iden g 
    ≅[ p ] 
    comp iden h 
    ≅[ idl ] 
    h 
    ∎

  compmonos : ∀{A B C}(f : Hom A B)(g : Hom B C) → Mono f → Mono g → Mono (comp g f)
  compmonos {A}{B}{C} f g p q {D}{h1}{h2} r = p $ q $
    proof 
    comp g (comp f h1)
    ≅[ sym ass ] 
    comp (comp g f) h1 
    ≅[ r ] 
    comp (comp g f) h2 
    ≅[ ass ] 
    comp g (comp f h2) 
    ∎


module Isos (X : Cat) where
  open Cat X

  Iso : ∀{A B} → Hom A B → Set
  Iso {A}{B} f = Σ (Hom B A) (λ g → comp f g ≅ iden {B} × comp g f ≅ iden {A})

  invuniq : ∀{A B}(f : Hom A B)(p q : Iso f) → proj₁ p ≅ proj₁ q
  invuniq f (g , p , p') (g' , q , q') = 
    proof 
    g 
    ≅[ sym idr ] 
    comp g iden
    ≅[ cong (comp g) (sym q) ] 
    comp g (comp f g')
    ≅[ sym ass ] 
    comp (comp g f) g'
    ≅[ cong (λ h → comp h g') p' ]     
    comp iden g'
    ≅[ idl ]     
    g'
    ∎

  open Monos X
  iso→mono : ∀{A B}{f : Hom A B} → Iso f → Mono f
  iso→mono {A}{B} {f} (f' , p , p') {C}{g}{h} q = 
    proof 
    g 
    ≅[ sym idl ] 
    comp iden g 
    ≅[ cong (λ h → comp h g) (sym p') ] 
    comp (comp f' f) g 
    ≅[ ass ] 
    comp f' (comp f g) 
    ≅[ cong (comp f') q ] 
    comp f' (comp f h) 
    ≅[ sym ass ] 
    comp (comp f' f) h 
    ≅[ cong (λ g → comp g h) p' ] 
    comp iden h 
    ≅[ idl ] 
    h 
    ∎

  compisos : ∀{A B C}{f : Hom A B}{g : Hom B C} → Iso f → Iso g → Iso (comp g f)
  compisos {A}{B}{C} {f} {g} (f' , p , p') (g' , q , q') = 
    (comp f' g') , 
    (proof 
     comp (comp g f) (comp f' g') 
     ≅[ ass ] 
     comp g (comp f (comp f' g')) 
     ≅[ cong (comp g) (sym ass) ] 
     comp g (comp (comp f f') g') 
     ≅[ cong (λ h → comp g (comp h g')) p ] 
     comp g (comp iden g') 
     ≅[ cong (comp g) idl ] 
     comp g g' 
     ≅[ q ] 
     iden 
     ∎) , 
    (proof 
     comp (comp f' g') (comp g f) 
     ≅[ ass ] 
     comp f' (comp g' (comp g f)) 
     ≅[ cong (comp f') (sym ass) ] 
     comp f' (comp (comp g' g) f) 
     ≅[ cong (λ h → comp f' (comp h f)) q' ] 
     comp f' (comp iden f) 
     ≅[ cong (comp f') idl ] 
     comp f' f 
     ≅[ p' ] 
     iden 
     ∎)
 

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
