{-# OPTIONS --type-in-type #-}
open import Categories
module Stable (X : Cat) where
  open import Relation.Binary.HeterogeneousEquality
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Data.Product
  open import Function
  open Cat X
  open import Pullbacks X
  open Monos X
  open Isos X
  open import PullbacksLemmas X

  record StableSys : Set where
    open Pullback
    open Square
    field ∈   : ∀{X Y}(f : Hom X Y) → Set
          mon : ∀{X Y}{f : Hom X Y} → ∈ f → Mono f
          iso : ∀{X Y}{f : Hom X Y} → Iso f → ∈ f 
          com : ∀{X Y Z}{f : Hom Z X}{g : Hom X Y} → ∈ f → ∈ g → ∈ (comp g f)
          pul : ∀{X Y Z}(f : Hom X Z){m : Hom Y Z} → ∈ m → 
                Σ (Pullback f m) λ p → ∈ (h (sq p))
  

  AllIsos : StableSys
  AllIsos = record { 
    ∈   = Iso; 
    mon = iso→mono; 
    iso = id; 
    com = compisos; 
    pul = λ f p → (iso→pullback p) , iden , idl , idl }


  module PartialCats (X : Cat)(M : StableSys) where

    open StableSys M

    record Span (A B : Obj) : Set where
      field A' : Obj
            mhom : Hom A' A
            fhom : Hom A' B
            m∈ : ∈ mhom

    open Span
--    open Pullback
--    open Square

    postulate cheat : ∀{A B}(mf m'f' : Span A B) → 
                      (s : Hom (A' mf) (A' m'f')) → 
                      Iso s → 
                      comp (mhom m'f') s ≅ (mhom mf) →
                      comp (fhom m'f') s ≅ (fhom mf) → 
                      mf ≅ m'f'

    Partials : Cat
    Partials = record {
                 Obj = Obj;
                 Hom = Span;
                 iden = λ {X} → record { 
                   A' = X; 
                   mhom = iden;
                   fhom = iden;
                   m∈ = iso (iden , idl , idl)};                
                 comp = λ {X}{Y}{Z} m'f' mf → 
                   let open Pullback
                       open Square
                       x = pul (fhom mf) (m∈ m'f')
                       y = sq (proj₁ x)
                   in record {
                     A' = W y; 
                     mhom = comp (mhom mf) (h y); 
                     fhom = comp (fhom m'f') (k y); 
                     m∈ = com (proj₂ x) (m∈ mf)};
                 idl = λ {X} {Y} {mf} → 
                   let open Pullback
                       open Square
                   in cheat 
                   _ 
                   _ 
                   (h (sq (proj₁ (pul (fhom mf)  (iso (iden , idl , idl)))))) 
                   (pullbackiso (trivialpul (fhom mf)) 
                                (proj₁ (pul (fhom mf) 
                                            (iso ((iden , idl , idl)))))) 
                   refl
                   (scom (sq (proj₁ (pul (fhom mf)
                                         (iso (iden , idl , idl))))));
                 idr = λ {X} {Y} {mf} → 
                   let open Pullback
                       open Square
                   in cheat 
                   _ 
                   _ 
                   (k (sq (proj₁ (pul iden (m∈ mf))))) 
                   (pullbackiso (trivialpul2 (mhom mf)) 
                                (proj₁ (pul iden (m∈ mf))))
                   (sym (scom (sq (proj₁ (pul iden (m∈ mf)))))) 
                   refl;
                 ass = λ {W} {X} {Y} {Z} {m''f''} {m'f'} {mf} → 
                 let open Span mf renaming (mhom to m ; fhom to f)
                     open Span m'f' renaming (mhom to m' ; fhom to f' ; m∈ to m'∈)
                     open Span m''f'' renaming (mhom to m'' ; fhom to f'' ; m∈ to m''∈)

                     bpul : Pullback f m'
                     bpul = proj₁ (pul f m'∈)
                 
                     open Pullback bpul
                     open Square sq renaming (W to B)

                     b'pul : Pullback (comp f' k) m''
                     b'pul = proj₁ (pul (comp f' k) m''∈)

                     open Pullback b'pul renaming (sq to sq' ; prop to prop')
                     open Square sq' renaming (W to B' ; h to h' ; k to k' ; scom to scom')

                     b''pul : Pullback f' m''
                     b''pul = proj₁ (pul f' m''∈)

                     open Pullback b''pul renaming (sq to sq'' ; prop to prop'')
                     open Square sq'' renaming (W to B'' ; h to h'' ; k to k'' ; scom to scom'')

                     b'''pul : Pullback f (comp m' h'')
                     b'''pul = proj₁ (pul f (com (proj₂ (pul f' m''∈)) m'∈))

                     open Pullback b'''pul renaming (sq to sq''' ; prop to prop''')
                     open Square sq''' renaming (W to B''' ; h to h''' ; k to k''' ; scom to scom''')

                     sqb' : Square f' m''
                     sqb' = record { 
                       W = B'; 
                       h = comp k h'; 
                       k = k'; 
                       scom = 
                         proof 
                         comp f' (comp k h') 
                         ≅⟨ sym ass ⟩ 
                         comp (comp f' k) h' 
                         ≅⟨ scom' ⟩ 
                         comp m'' k' 
                         ∎ }

                     pu : PMap sqb' sq''
                     pu = proj₁ (prop'' sqb')

                     open PMap pu renaming (mor to u)

                     sqb''' : Square f m'
                     sqb''' = record { 
                       W = B'''; 
                       h = h'''; 
                       k = comp h'' k'''; 
                       scom = 
                         proof 
                         comp f h''' 
                         ≅⟨ scom''' ⟩ 
                         comp (comp m' h'') k''' 
                         ≅⟨ ass ⟩ 
                         comp m' (comp h'' k''') 
                         ∎ }

                     pu' : PMap sqb''' sq
                     pu' = proj₁ (prop sqb''')

                     open PMap pu' renaming (mor to u' ; prop1 to prop1' ; prop2 to prop2')

                     upul : Pullback k h''
                     upul = lem2 b'pul b''pul u (sym prop1) (sym prop2)

                     u'pul : Pullback k h''
                     u'pul = {!!} 

                     open Pullback upul renaming (sq to usq ; prop to uprop)
                     open Pullback u'pul renaming (sq to u'sq ; prop to u'prop)

                     pα : PMap u'sq usq
                     pα = proj₁ (uprop u'sq)

                     open PMap pα renaming (mor to α ; prop1 to prop1α ; prop2 to prop2α)
                     
                 in cheat 
                   _ 
                   _ 
                   α 
                   (pullbackiso upul u'pul) 
                   (proof 
                    comp (comp (comp m h) h') α 
                    ≅⟨ ass ⟩ 
                    comp (comp m h) (comp h' α)
                    ≅⟨ cong (comp (comp m h)) prop1α ⟩ 
                    comp (comp m h) u'
                    ≅⟨ ass ⟩ 
                    comp m (comp h u')
                    ≅⟨ cong (comp m) prop1' ⟩ 
                    comp m h'''
                    ∎) 
                   (proof 
                    comp (comp f'' k') α
                    ≅⟨ cong (λ y → comp (comp f'' y) α) (sym prop2) ⟩ 
                    comp (comp f'' (comp k'' u)) α 
                    ≅⟨ cong (λ y → comp y α) (sym ass) ⟩ 
                    comp (comp (comp f'' k'') u) α
                    ≅⟨ ass ⟩ 
                    comp (comp f'' k'') (comp u α)
                    ≅⟨ cong (comp (comp f'' k'')) prop2α ⟩ 
                    comp (comp f'' k'') k'''
                    ∎)}
