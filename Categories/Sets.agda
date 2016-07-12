{-# OPTIONS --type-in-type #-}
module Categories.Sets where
open import Utilities
open import Categories

Sets : Cat
Sets = record {
         Obj  = Set;
         Hom  = λ X Y → X → Y;
         iden = id;
         comp = λ g f → g ∘ f;
         idl  = refl;
         idr  = refl;
         ass  = refl}
