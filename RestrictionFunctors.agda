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

record RestFun (X Y : RestCat) : Set where
  open Cat
  open RestCat
  open Fun
  field fun   : Fun (cat X) (cat Y)
        .frest : ∀{A B}{f : Hom (cat X) A B} → 
                rest Y (HMap fun f) ≅ HMap fun (rest X f)

F : ∀{X} → Fun (Totals.Total X) (RestCat.cat X)
F {X} = record { 
  OMap  = id; 
  HMap  = hom; 
  fid   = refl;
  fcomp = refl}
  where open Totals X
        open Tot

RF : ∀{X} → RestFun (Trivial (Totals.Total X)) X
RF {X} = record { 
  fun   = F; 
  frest = λ {_ _ f} → tot f }
  where open Totals X
        open Tot

.RFFaithful : ∀{X} → Faithful (F {X})
RFFaithful {X} = λ {_} {_} {f} {g} → TotEq f g
  where open Totals X
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

postulate .RFun≅ : ∀{C D}{F G : RestFun C D} → RestFun.fun F ≅ RestFun.fun G → F ≅ G
