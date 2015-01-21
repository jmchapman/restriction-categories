{-# OPTIONS --type-in-type #-}
module Restriction.Functors where

open import Categories
open import Utilities
open import Restriction.Cat
open import Categories.Functors
--import Restriction.Totals
open RestCat
open Cat
open Fun 

record RestFun (X Y : RestCat) : Set where
  field fun   : Fun (cat X) (cat Y)
        frest : ∀{A B}{f : Hom (cat X) A B} → 
                rest Y (HMap fun f) ≅ HMap fun (rest X f)

open RestFun

idRestFun : ∀{C} → RestFun C C
idRestFun {C} = record { 
  fun = idFun; 
  frest = refl }

_○R_ : ∀{C D E} → RestFun D E → RestFun C D → RestFun C E
_○R_ {C}{D}{E} G F = record { 
  fun = fun G ○ fun F; 
  frest = λ {_}{_}{f} → 
    proof
    rest E (HMap (fun G) (HMap (fun F) f))
    ≅⟨ frest G ⟩
    HMap (fun G) (rest D (HMap (fun F) f))
    ≅⟨ cong (HMap (fun G)) (frest F) ⟩
    HMap (fun G) (HMap (fun F) (rest C f))
    ∎}

{-
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
    (iext (λ X → iext (λ Y → iext (λ f → hir'
      (cong (λ F → HMap F (rest C f)) p)))))


RCCat : Cat
RCCat = record {
         Obj = RestCat;
         Hom = RestFun;
         iden = IdRF;
         comp = _○R_;
         idl = RFun≅ (Fun≅ refl (λ _ → refl));
         idr = RFun≅ (Fun≅ refl (λ _ → refl));
         ass = RFun≅ (Fun≅ refl (λ _ → refl)) }
-}



{-
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
RFFaithful {X} = TotEq
  where open Restriction.Totals X
        open Tot
-}
