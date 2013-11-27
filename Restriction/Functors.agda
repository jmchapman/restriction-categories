module Restriction.Functors where

open import Categories
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open ≅-Reasoning renaming (begin_ to proof_)
open import Function
open import Data.Product
open import Restriction.Cat
open import Categories.Functors
import Restriction.Totals

record RestFun (X Y : RestCat) : Set where
  open Cat
  open RestCat
  open Fun
  field fun   : Fun (cat X) (cat Y)
        .frest : ∀{A B}{f : Hom (cat X) A B} → 
                rest Y (HMap fun f) ≅ HMap fun (rest X f)

F : ∀{X} → Fun (Restriction.Totals.Total X) (RestCat.cat X)
F {X} = record { 
  OMap  = id; 
  HMap  = hom; 
  fid   = refl;
  fcomp = refl}
  where open Restriction.Totals X
        open Tot

RF : ∀{X} → RestFun (Trivial (Restriction.Totals.Total X)) X
RF {X} = record { 
  fun   = F; 
  frest = λ {_ _ f} → tot f }
  where open Restriction.Totals X
        open Tot

.RFFaithful : ∀{X} → Faithful (F {X})
RFFaithful {X} = λ {_} {_} {f} {g} → TotEq f g
  where open Restriction.Totals X
        open Tot

-- Cat of Restriction Cats

open RestFun
open RestCat
open Fun 

IdRF : ∀{C} → RestFun C C
IdRF {C} = record { 
  fun = IdF (cat C); 
  frest = refl }

_○R_ : ∀{C D E} → RestFun D E → RestFun C D → RestFun C E
_○R_ {C}{D}{E} F G = record { 
  fun = fun F ○ fun G; 
  frest = λ {A}{B}{f} → 
    proof
    rest E (HMap (fun F) (HMap (fun G) f))
    ≅⟨ frest F ⟩
    HMap (fun F) (rest D (HMap (fun G) f))
    ≅⟨ cong (HMap (fun F)) (frest G) ⟩
    HMap (fun F) (HMap (fun G) (rest C f))
    ∎}

RCCat : Cat
RCCat = record {
         Obj = RestCat;
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
