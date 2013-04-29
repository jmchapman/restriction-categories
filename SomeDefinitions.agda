{-# OPTIONS --type-in-type #-}

module SomeDefinitions where

open import Relation.Binary.HeterogeneousEquality
open import Equality
open ≅-Reasoning renaming (begin_ to proof_)
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

module Idems (X : Cat) where
  open Cat X

  record Idem : Set where
    field E : Obj
          e : Hom E E
          law : comp e e ≅ e

  record Split (ide : Idem) : Set where
    open Idem ide
    field B : Obj 
          s : Hom B E
          r : Hom E B
          law1 : comp s r ≅ e
          law2 : comp r s ≅ iden {B}

module Pullbacks (X : Cat) where
  open Cat X

  record Square {X Y Z}(f : Hom X Z)(g : Hom Y Z) : Set where
     field W    : Obj
           h    : Hom W X
           k    : Hom W Y
           scom : comp f h ≅ comp g k

  record PMap  {X Y Z : Obj}{f : Hom X Z}{g : Hom Y Z}(sq' sq : Square f g) 
         : Set where
    open Square
    field mor   : Hom (W sq') (W sq)
          prop1 : comp (h sq) mor ≅ h sq'
          prop2 : comp (k sq) mor ≅ k sq'
  open PMap


  record Pullback {X Y Z}(f : Hom X Z)(g : Hom Y Z) : Set where
    field sq : Square f g
          prop : (sq' : Square f g) → 
                 Σ (PMap sq' sq) λ u → (u' : PMap sq' sq) → mor u ≅  mor u'

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

module Totals (X : RestCat) where
  open RestCat X
  open Cat cat
  open Monos

  record Tot (A B : Obj) : Set where
    field hom : Hom A B 
          tot : rest hom ≅ iden {A}
