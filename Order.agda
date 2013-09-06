open import RestrictionCat

module Order {a b}(X : RestCat {a}{b}) where

open import Categories
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open ≅-Reasoning renaming (begin_ to proof_)
open RestCat X
open Cat cat
open import Level
open import Function

infix 4 _≤_

_⌣_ : ∀{A B} → Hom A B → Hom A B → Set
f ⌣ g = comp g (rest f) ≅ comp f (rest g)

.comp⌣ : ∀{A B C}{f g : Hom A B}(p : f ⌣ g){h : Hom C _} → comp f h ⌣ comp g h
comp⌣ {f = f}{g = g} p {h = h} = 
  proof
  comp (comp g h) (rest (comp f h))
  ≅⟨ ass ⟩
  comp g (comp h (rest (comp f h)))
  ≅⟨ cong (comp g) (sym R4) ⟩
  comp g (comp (rest f) h)
  ≅⟨ sym ass ⟩
  comp (comp g (rest f)) h
  ≅⟨ cong (λ x → comp x h) p ⟩
  comp (comp f (rest g)) h
  ≅⟨ ass ⟩
  comp f (comp (rest g) h)
  ≅⟨ cong (comp f) R4 ⟩
  comp f (comp h (rest (comp g h)))
  ≅⟨ sym ass ⟩
  comp (comp f h) (rest (comp g h))  
  ∎

_≤_ : ∀{A B} → Hom A B → Hom A B → Set
f ≤ g = comp g (rest f) ≅ f

.refl≤ : ∀{A B}{f : Hom A B} → f ≤ f
refl≤ {f = f} = R1

.trans≤ : ∀{A B}{f g h : Hom A B} → f ≤ g → g ≤ h → f ≤ h
trans≤ {f = f}{g = g}{h = h} p q = 
  proof 
  comp h (rest f)
  ≅⟨ cong (comp h ∘ rest) (sym p) ⟩
  comp h (rest (comp g (rest f)))
  ≅⟨ cong (comp h) (sym R3) ⟩
  comp h (comp (rest g) (rest f))
  ≅⟨ sym ass ⟩
  comp (comp h (rest g)) (rest f)
  ≅⟨ cong (λ x → comp x (rest f)) q ⟩
  comp g (rest f)
  ≅⟨ p ⟩
  f
  ∎

.antisym≤ : ∀{A B}{f g : Hom A B} → f ≤ g → g ≤ f → f ≅ g
antisym≤ {f = f}{g = g} p q =
  proof 
  f
  ≅⟨ sym p ⟩
  comp g (rest f)
  ≅⟨ cong (λ x → comp x (rest f)) (sym R1) ⟩
  comp (comp g (rest g)) (rest f)
  ≅⟨ ass ⟩
  comp g (comp (rest g) (rest f))
  ≅⟨ cong (comp g) R2 ⟩
  comp g (comp (rest f) (rest g))
  ≅⟨ cong (comp g) R3 ⟩
  comp g (rest (comp f (rest g)))
  ≅⟨ cong (comp g ∘ rest) q ⟩
  comp g (rest g)
  ≅⟨ R1 ⟩
  g
  ∎

module Meets where

  record Meet : Set (a ⊔ b) where
    field _∩_  : ∀{A B} → Hom A B → Hom A B → Hom A B
          Mt1  : ∀{A B}{f : Hom A B} → f ∩ f ≅ f
          Mt2a : ∀{A B}{f g : Hom A B} → f ∩ g ≤ g
          Mt2b : ∀{A B}{f g : Hom A B} → f ∩ g ≤ f
          Mt3  : ∀{A B C}{f g : Hom A B}{h : Hom C A} → 
                 comp (f ∩ g) h ≅ comp f h ∩ comp g h

  MeetIsMeet : ∀{A B}{f g h : Hom A B}(m : Meet) → 
               let open Meet m
               in h ≤ f → h ≤ g → h ≤ f ∩ g
  MeetIsMeet {f = f}{g = g}{h = h} m p q = 
    let open Meet m
    in proof
       comp (f ∩ g) (rest h)
       ≅⟨ Mt3 ⟩
       comp f (rest h) ∩ comp g (rest h)
       ≅⟨ cong (λ x → x ∩ comp g (rest h)) p ⟩
       h ∩ comp g (rest h)
       ≅⟨ cong (_∩_ h) q ⟩
       h ∩ h
       ≅⟨ Mt1 ⟩
       h
       ∎

module Joins where

  record Join : Set (a ⊔ b) where
    field _∨_∣_ : ∀{A B}(f g : Hom A B) → .(f ⌣ g) → Hom A B
          Jn1a  : ∀{A B}{f g : Hom A B}{p : f ⌣ g} → f ≤ f ∨ g ∣ p
          Jn1b  : ∀{A B}{f g : Hom A B}{p : f ⌣ g} → g ≤ f ∨ g ∣ p
          Jn2   : ∀{A B}{f g h : Hom A B}{p : f ⌣ g} → f ≤ h  → g ≤ h → 
                  f ∨ g ∣ p ≤ h
          Jn3   : ∀{A B C}{f g : Hom A B}{p : f ⌣ g}{h : Hom C _} →
                  comp (f ∨ g ∣ p) h ≅ (comp f h) ∨ (comp g h) ∣ comp⌣ p
