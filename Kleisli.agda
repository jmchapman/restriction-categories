module Kleisli where

open import Categories
open import Monads
open import Relation.Binary.PropositionalEquality

Kl : ∀{C} → Monad C → Cat
Kl {C} M = record{
  Obj  = Obj;
  Hom  = λ X Y → Hom X (T Y);
  iden = η;
  comp = λ f g → comp (bind f) g;
  idl  = λ{X}{Y}{f} → trans (cong (λ g → comp g f) law1) idl;
  idr  = law2;
  ass  = λ{W}{X}{Y}{Z}{f}{g}{h} →
    trans (cong (λ (f : Hom (T X) (T Z)) → comp f h) law3) ass}
  where open Cat C
        open Monad M