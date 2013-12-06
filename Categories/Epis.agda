open import Categories

module Categories.Epis (X : Cat) where
  open import Utilities

  open Cat X

  Epi : ∀{A B} → Hom A B → Set
  Epi f = ∀{C}{g h : Hom _ C} → comp g f ≅ comp h f → g ≅ h
