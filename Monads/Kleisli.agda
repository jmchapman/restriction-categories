module Monads.Kleisli where

open import Categories
open import Monads
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)

Kl : ∀{C} → Monad C → Cat
Kl {C} M = record{
  Obj  = Obj;
  Hom  = λ X Y → Hom X (T Y);
  iden = η;
  comp = λ f g → comp (bind f) g;
  idl  = λ{_}{_}{f} → 
    proof 
    comp (bind η) f 
    ≅⟨ cong (λ g → comp g f) law1 ⟩ 
    comp iden f 
    ≅⟨ idl ⟩ 
    f 
    ∎; 
  idr  = λ{_}{_}{f} → 
    proof 
    comp (bind f) η 
    ≅⟨ law2 ⟩ 
    f
    ∎;
  ass  = λ{_}{_}{_}{_}{f}{g}{h} → 
    proof
    comp (bind (comp (bind f) g)) h 
    ≅⟨ cong (λ f → comp f h) law3 ⟩
    comp (comp (bind f) (bind g)) h
    ≅⟨ ass ⟩
    comp (bind f) (comp (bind g) h) 
    ∎}
  where open Cat C
        open Monad M