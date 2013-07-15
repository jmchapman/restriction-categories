
module Categories where

open import Relation.Binary.HeterogeneousEquality
open import Level

record Cat {a b} : Set (suc (a ⊔ b)) where
  field Obj  : Set a
        Hom  : Obj → Obj → Set b
        iden : ∀{X} → Hom X X
        comp : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        .idl  : ∀{X Y}{f : Hom X Y} → comp iden f ≅ f
        .idr  : ∀{X Y}{f : Hom X Y} → comp f iden ≅ f
        .ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
               comp (comp f g) h ≅ comp f (comp g h)

_Op : ∀{a b} → Cat {a}{b}→ Cat {a}{b}
C Op = record {
  Obj  = Obj; 
  Hom  = λ X Y → Hom Y X;
  iden = iden;
  comp = λ f g → comp g f; 
  idl  = idr;
  idr  = idl;
  ass  = sym ass}
  where open Cat C

DiscreteCat : ∀{X : Set} → Cat {zero}{zero}
DiscreteCat {X} = 
  record {
    Obj = X;
    Hom = λ x y → x ≅ y;
    iden = refl;
    comp = λ p q → trans q p;
    idl = idl _;
    idr = refl;
    ass = λ {_}{_}{_}{_}{_}{_}{h} → ass _ _ h }
  where   
  idl : {x y : X}(f : x ≅ y) → trans f refl ≅ f
  idl refl = refl

  ass : {w x y z : X}(f : y ≅ z)(g : x ≅ y)(h : w ≅ x) →
        trans h (trans g f) ≅ trans (trans h g) f
  ass f g refl = refl
