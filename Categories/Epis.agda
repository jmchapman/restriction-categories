open import Categories

module Categories.Epis {a b}(X : Cat {a}{b}) where
  open import Relation.Binary.HeterogeneousEquality
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Function
  open import Level

  open Cat X

  Epi : ∀{A B} → Hom A B → Set (a ⊔ b)
  Epi f = ∀{C}{g h : Hom _ C} → comp g f ≅ comp h f → g ≅ h
