module Categories.StrongFuns where

open import Categories
open import Utilities
open import Categories.Functors
open import Categories.ProductCats
open import Categories.Products

record StrongFun (C : ProdCat) : Set where
  open ProdCat C
  field fun : Fun cat cat
  open Fun fun
  open Cat cat
  field str : ∀{A B} → Hom (A ×' OMap B) (OMap (A ×' B))
--        nat : ∀{A B A' B'}{f : Hom A A'}{g : Hom B B'} → comp 
