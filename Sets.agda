
module Sets where

open import Categories
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Level

Sets : ∀{a} → Cat {suc a}{a}
Sets {a} = record {
         Obj  = Set a;
         Hom  = λ X Y → X → Y;
         iden = id;
         comp = λ g f → g ∘ f;
         idl  = refl;
         idr  = refl;
         ass  = refl}
