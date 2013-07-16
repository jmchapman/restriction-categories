module RestrictionFunctors where

open import Categories
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open ≅-Reasoning renaming (begin_ to proof_)
open import Function
open import Data.Product
open import RestrictionCat
open import Functors
import Totals
open import Level

record RestFun {a b}(X Y : RestCat {a}{b}) : Set (a ⊔ b) where
  open Cat
  open RestCat
  open Fun
  field fun   : Fun (cat X) (cat Y)
        .frest : ∀{A B}{f : Hom (cat X) A B} → 
                rest Y (HMap fun f) ≅ HMap fun (rest X f)

F : ∀{a b}{X : RestCat {a}{b}} → Fun (Totals.Total X) (RestCat.cat X)
F {_}{_}{X} = record { 
  OMap  = id; 
  HMap  = hom; 
  fid   = refl;
  fcomp = refl}
  where open Totals X
        open Tot

RF : ∀{a b}{X : RestCat {a}{b}} → RestFun (Trivial (Totals.Total X)) X
RF {_}{_}{X} = record { 
  fun   = F; 
  frest = λ {_ _ f} → tot f }
  where open Totals X
        open Tot

.RFFaithful : ∀{a b}{X : RestCat {a}{b}} → Faithful F
RFFaithful {_}{_}{X} = λ {_} {_} {f} {g} → TotEq f g
  where open Totals X
        open Tot

-- Cat of Restriction Cats

open RestFun
open RestCat
open Fun 

IdRF : ∀{a b}{C : RestCat {a}{b}} → RestFun C C
IdRF {_}{_}{C} = record { 
  fun = IdF (cat C); 
  frest = refl }

_○R_ : ∀{a b}{C D E : RestCat {a}{b}} → RestFun D E → RestFun C D → RestFun C E
_○R_ {_}{_}{C}{D}{E} F G = record { 
  fun = fun F ○ fun G; 
  frest = λ {A}{B}{f} → 
    proof
    rest E (HMap (fun F) (HMap (fun G) f))
    ≅⟨ frest F ⟩
    HMap (fun F) (rest D (HMap (fun G) f))
    ≅⟨ cong (HMap (fun F)) (frest G) ⟩
    HMap (fun F) (HMap (fun G) (rest C f))
    ∎}

RCCat : ∀{a b} → Cat {suc a ⊔ suc b}{a ⊔ b}
RCCat {a}{b} = record {
         Obj = RestCat {a}{b};
         Hom = RestFun;
         iden = IdRF;
         comp = _○R_;
         idl = refl;
         idr = refl;
         ass = refl }
{-
record RestFun (X Y : RestCat) : Set where
  open Cat
  open RestCat
  open Fun
  field fun   : Fun (cat X) (cat Y)
        .frest : ∀{A B}{f : Hom (cat X) A B} → 
                rest Y (HMap fun f) ≅ HMap fun (rest X f)
-}


.RFun≅ : ∀{C D}{F G : RestFun C D} → RestFun.fun F ≅ RestFun.fun G → F ≅ G
RFun≅ {C}{D}{F}{G} p  = 
  let
    open Cat
    open RestCat
    open Fun
  in cong₂ 
    {A = Fun (cat C) (cat D)}
    {B = λ fun₁ → {A B : _} {f : Hom (cat C) A B} →
           rest D (HMap fun₁ f) ≅ HMap fun₁ (rest C f)}
    {C = λ _ _ → RestFun C D}
    {u = RestFun.frest F}
    {v = RestFun.frest G}
    (λ x y → record { fun = x; frest = y }) 
    p
    (iext (λ X → iext (λ Y → iext (λ f → fixtypes 
      (cong₃ 
        (cong (λ F → OMap F X) p)
        (cong (λ F → OMap F Y) p) 
        (cong (λ F → HMap F f) p) 
        (λ x y z → rest D {x} {y} z)) 
      (cong (λ F → HMap F (rest C f)) p)))))
