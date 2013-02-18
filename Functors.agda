{-# OPTIONS --type-in-type #-}
module Functors where

open import Relation.Binary.HeterogeneousEquality
open import Function
open import Categories
open ≅-Reasoning

record Fun (C D : Cat) : Set where
  open Cat
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (comp C f g) ≅ comp D (HMap f) (HMap g)
open Fun

IdF : ∀ C → Fun C C
IdF C = record{OMap = id;HMap = id;fid = refl;fcomp = refl}

_○_ : ∀{C D E} → Fun D E → Fun C D → Fun C E
_○_ {C}{D}{E} F G = record{OMap  = OMap F ∘ OMap G;
                           HMap  = HMap F ∘ HMap G;
                           fid   = begin 
                                   HMap F (HMap G (iden C)) 
                                   ≅⟨ cong (HMap F) (fid G) ⟩
                                   HMap F (iden D)
                                   ≅⟨ fid F ⟩ 
                                   iden E 
                                   ∎;
                           fcomp = λ {X}{Y}{Z}{f}{g} → 
                                   begin
                                   HMap F (HMap G (comp C f g)) 
                                   ≅⟨ cong (HMap F) (fcomp G)  ⟩ 
                                   HMap F (comp D (HMap G f) (HMap G g))
                                   ≅⟨ fcomp F ⟩ 
                                   comp E (HMap F (HMap G f)) 
                                          (HMap F (HMap G g)) 
                                   ∎}
  where open Cat

