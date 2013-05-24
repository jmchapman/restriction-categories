{-# OPTIONS --type-in-type #-}

module ProductCats where

open import Categories
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open ≅-Reasoning renaming (begin_ to proof_)
open import Products

record ProdCat : Set where
  field cat  : Cat
  open  Cat cat
  field prod : ∀(A B : Obj) → Prod cat A B
        termobj : TermObj cat

  open Prod cat
  _×_ : ∀(A B : Obj) → Obj
  _×_ A B = W (prod A B)

