{-# OPTIONS --type-in-type #-}
module RestrictionCat where

open import Categories
open import Relation.Binary.PropositionalEquality

record RestCat : Set where
  field cat  : Cat
  open  Cat cat
  field rest : ∀{A B} → Hom A B → Hom A A
        R1   : ∀{A B}{f : Hom A B} → comp f (rest f) ≡ f 
        R2   : ∀{A B C}{f : Hom A B}{g : Hom A C} →
               comp (rest f) (rest g) ≡ comp (rest g) (rest f)
        R3   : ∀{A B C}{f : Hom A B}{g : Hom A C} →
               rest (comp g (rest f)) ≡ comp (rest f) (rest g)
        R4   : ∀{A B C}{f : Hom A B}{g : Hom B C} →
               comp (rest g) f ≡ comp  f (rest (comp g f))


Trivial : Cat → RestCat
Trivial C = record { 
  cat  = C; 
  rest = λ _ → iden; 
  R1   = idr; 
  R2   = trans idr (sym idl); 
  R3   = sym idr; 
  R4   = trans idl (sym idr)} 
  where open Cat C

