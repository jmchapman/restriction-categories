
module Categories where

open import Utilities

record Cat {i j} : Set (suc (i ⊔ j)) where
  field Obj  : Set i
        Hom  : Obj → Obj → Set j
        iden : ∀{X} → Hom X X
        comp : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → comp iden f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → comp f iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
               comp (comp f g) h ≅ comp f (comp g h)

_Op : ∀{i j} → Cat {i}{j}→ Cat
C Op = record {
  Obj  = Obj; 
  Hom  = λ X Y → Hom Y X;
  iden = iden;
  comp = λ f g → comp g f; 
  idl  = idr;
  idr  = idl;
  ass  = sym ass}
  where open Cat C
