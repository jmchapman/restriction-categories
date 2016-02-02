module Restriction.SplitRestCats where

open import Utilities
open import Categories
open import Restriction.Cat
open import Categories.Idems
open import Categories.Splits
open import Restriction.Idems

 -- split restriction category

record SplitRestCat : Set where
  field rcat          : RestCat
  field restIdemSplit : (i : Idem (RestCat.cat rcat)) → isRestIdem rcat i → 
                        Split (RestCat.cat rcat) i
