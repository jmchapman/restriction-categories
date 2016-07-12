open import Categories

module Categories.Epis {i j}(X : Cat {i}{j}) where

open import Utilities
open Cat X

Epi : ∀{A B} → Hom A B → Set (i ⊔ j)
Epi f = ∀{C}{g h : Hom _ C} → comp g f ≅ comp h f → g ≅ h
