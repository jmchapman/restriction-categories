{-# OPTIONS --type-in-type #-}
module Functors where

open import Relation.Binary.PropositionalEquality
open import Function
open import Categories
open ≡-Reasoning

record Fun (C D : Cat) : Set where
  open Cat
  field OMap  : ! C ! → ! D !
        HMap  : ∀{X Y} → C < X , Y > → D < OMap X , OMap Y >
        fid   : ∀{X} → HMap (iden C {X}) ≡ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : C < Y , Z >}{g : C < X , Y >} → 
                HMap (C ! f • g) ≡ D ! HMap f • HMap g

open Fun

_`_ : ∀{C D}(F : Fun C D) → ! C ! → ! D !
F ` X = OMap F X

_``_ : ∀{C D}(F : Fun C D) → ∀{X Y} → C < X , Y > → D < F ` X , F ` Y >
F `` f = HMap F f

IdF : ∀ C → Fun C C
IdF C = record{OMap = id;HMap = id;fid = refl;fcomp = refl}

-- here's an example of the equational reasoning style
-- I have recently learnt that putting proofs inside record defs like 
-- this is very bad for performance

-- fancy syntax seems to get in the way already below, you can't use it partially applied
_○_ : ∀{C D E} → Fun D E → Fun C D → Fun C E
_○_ {C}{D}{E} F G = record{OMap  = OMap F ∘ OMap G;
                           HMap  = HMap F ∘ HMap G;
                           fid   = begin 
                                   HMap F (HMap G (iden C)) 
                                   ≡⟨ cong (HMap F) (fid G) ⟩
                                   HMap F (iden D)
                                   ≡⟨ fid F ⟩ 
                                   iden E 
                                   ∎;
                           fcomp = λ {X}{Y}{Z}{f}{g} → 
                                   begin
                                   HMap F (HMap G (comp C f g)) 
                                   ≡⟨ cong (HMap F) (fcomp G)  ⟩ 
                                   HMap F (comp D (HMap G f) (HMap G g))
                                   ≡⟨ fcomp F ⟩ 
                                   comp E (HMap F (HMap G f)) (HMap F (HMap G g)) 
                                   ∎}
  where open Cat

-- Not sure if we'll need this, if we do we will need a EqualityExtras file

{-
FunctorEq : ∀{C D}(F G : Fun C D) → 
            OMap F ≡ OMap G → 
            (∀{X Y}(f : Hom C X Y) → HMap F f ≡ HMap G f) → 
            F ≡ G
FunctorEq {C}{D} F G p q = funnyresp4'
  {Obj C → Obj D}
  {λ OMap → ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)}
  {λ OMap HMap → ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}}
  {λ OMap HMap → ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → HMap (comp C f g) ≅ comp D (HMap f) (HMap g)}
  p
  (iext λ X → iext λ Y → ext λ f → q f)
  (iext λ X → fixtypes 
    (q (iden C))
    (iresp (λ {X} → iden D {X}) (fresp X p)))
  (iext λ X → iext λ Y → iext λ Z → iext λ f → iext λ g → fixtypes 
    (q (comp C f g)) 
    (trans (trans (sym (fcomp F)) (q (comp C f g))) (fcomp G)))
  λ w x y z → record{OMap = w;HMap = x;fid = y; fcomp = z} 
-}