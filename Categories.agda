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

module Pullbacks (X : Cat) where
  open Cat X

  record Square {X Y Z}(f : Hom Y Z)(g : Hom X Z) : Set where
     field W    : Obj
           h    : Hom W Y
           k    : Hom W X
           scom : comp f h ≅ comp g k
  open Square

{-
  PMap : ∀{X Y Z}{f : Hom Y Z}{g : Hom X Z}(sq sq' : Square f g) → Hom (W sq') (W sq) → Set
  PMap sq sq' u = comp (h sq) u ≅ h sq' × comp (k sq) u ≅ k sq'

  record Pullback {X Y Z}(f : Hom Y Z)(g : Hom X Z) : Set where
    field sq : Square f g
          prop : {sq' : Square f g} →
                   Σ (Hom (W sq') (W sq))
                     (λ u → PMap sq sq' u × (∀ u' → PMap sq sq' u' → u ≅ u')) 
-}

  record PMap  {X Y Z : Obj}{f : Hom Y Z}{g : Hom X Z}(sq sq' : Square f g) : Set where
    field mor   : Hom (W sq') (W sq)
          prop1 : comp (h sq) mor ≅ h sq'
          prop2 : comp (k sq) mor ≅ k sq'
  open PMap

  record Pullback {X Y Z}(f : Hom Y Z)(g : Hom X Z) : Set where
    field sq : Square f g
          prop : {sq' : Square f g} → Σ (PMap sq sq') λ u → (u' : PMap sq sq') → mor u ≅  mor u'



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