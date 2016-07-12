{-# OPTIONS --type-in-type #-}

module Categories.ProductCats where
open import Utilities
open import Categories
open import Categories.Products

record ProdCat : Set where
  field cat  : Cat
  open  Cat cat
  field prod : ∀(A B : Obj) → Prod cat A B
        termobj : TermObj cat

  open Prod cat
  _×'_ : ∀(A B : Obj) → Obj
  _×'_ A B = W (prod A B)

