
module StrongFuns where

open import Categories
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open ≅-Reasoning renaming (begin_ to proof_)
open import Functors
open import ProductCats
open import Products

record StrongFun (C : ProdCat) : Set where
  open ProdCat C
  field fun : Fun cat cat
  open Fun fun
  open Cat cat
  field str : ∀{A B} → Hom (A × OMap B) (OMap (A × B))
        nat : ∀{A B A' B'}{f : Hom A A'}{g : Hom B B'} → comp 