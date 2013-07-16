
module Functors where

open import Relation.Binary.HeterogeneousEquality
open import Function
open import Categories
open ≅-Reasoning renaming (begin_ to proof_)
open import Data.Product
open import Utilities
open import Level

record Fun {a b}(C D : Cat {a}{b}) : Set (a ⊔ b) where
  open Cat
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        .fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        .fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (comp C f g) ≅ comp D (HMap f) (HMap g)

IdF : ∀{a b}(C : Cat {a}{b}) → Fun C C
IdF C = record {OMap = id; HMap = id; fid = refl; fcomp = refl}

open Fun
open Cat

.○fid : ∀{a b}{C D E : Cat {a}{b}} (F : Fun D E)(G : Fun C D){X : Obj C} →
       HMap F (HMap G (iden C {X})) ≅ iden E {OMap F (OMap G X)}
○fid {_}{_}{C}{D}{E} F G =  
  proof
  HMap F (HMap G (iden C)) 
  ≅⟨ cong (HMap F) (fid G) ⟩
  HMap F (iden D)
  ≅⟨ fid F ⟩ 
  iden E 
  ∎ 

.○fcomp : ∀{a b}{C D E : Cat {a}{b}} (F : Fun D E)(G : Fun C D)
  {X Y Z : Obj C} {f : Hom C Y Z}{g : Hom C X Y} →
  (HMap F ∘ HMap G) (comp C f g) 
  ≅ 
  comp E ((HMap F ∘ HMap G) f) ((HMap F ∘ HMap G) g)
○fcomp {_}{_}{C}{D}{E} F G {f = f}{g = g} =
  proof
  HMap F (HMap G (comp C f g)) 
  ≅⟨ cong (HMap F) (fcomp G) ⟩ 
  HMap F (comp D (HMap G f) (HMap G g))
  ≅⟨ fcomp F ⟩ 
  comp E (HMap F (HMap G f))(HMap F (HMap G g)) 
  ∎

_○_ : ∀{a b}{C D E : Cat {a}{b}} → Fun D E → Fun C D → Fun C E
F ○ G = record{
  OMap  = OMap F ∘ OMap G;
  HMap  = HMap F ∘ HMap G;
  fid   = ○fid F G;
  fcomp = ○fcomp F G}

Faithful : ∀{a b}{C D : Cat {a}{b}} → Fun C D → Set (a ⊔ b)
Faithful {_}{_}{C} F = ∀{A B}{f g : Hom C A B} → HMap F f ≅ HMap F g → f ≅ g

Full : ∀{a b}{C D : Cat {a}{b}} → Fun C D → Set (a ⊔ b)
Full {_}{_}{C}{D} F = ∀{A B}{f : Hom D (OMap F A) (OMap F B)} → Σ' (Hom C A B) λ g → HMap F g ≅ f

-- Equality for functors
.Fun≅ : ∀{C D}{F G : Fun C D} → Fun.OMap F ≅ Fun.OMap G →
       (∀{X Y}(f : Hom C X Y) → Fun.HMap F f ≅ Fun.HMap G f) → F ≅ G
Fun≅ {C}{D}{F}{G} p q = cong₄
  {Obj C → Obj D}
  {λ OMap → ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)}
  {λ OMap HMap → ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}}
  {λ OMap HMap → ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → HMap (comp C f g) ≅ comp D (HMap f) (HMap g)}
  {Fun C D}
  {Fun.OMap F}
  {Fun.OMap G} 
  p
  {Fun.HMap F}
  {Fun.HMap G} 
  (iext (λ X → iext (λ Y → ext q)))
  {Fun.fid F}
  {Fun.fid G}  
  (iext (λ X → fixtypes' (q (iden C))))
  {Fun.fcomp F}
  {Fun.fcomp G} 
  (iext (λ X → iext (λ Y → iext (λ Z → iext (λ f → iext (λ g → fixtypes' (q (comp C f g))))))))
  λ w x y z → record{OMap = w;HMap = x;fid = y; fcomp = z} 

-- Cat of Cats
CCat : ∀{a b} → Cat {suc b ⊔ suc a}{b ⊔ a}
CCat {a}{b} = record {
         Obj = Cat {a}{b};
         Hom = Fun;
         iden = λ {C} → IdF C;
         comp = _○_;
         idl = refl;
         idr = refl;
         ass = refl }
