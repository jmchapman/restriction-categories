
open import Categories
open import Stable
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Utilities
open import Data.Product
open import Function


module PartialMaps (X : Cat)(M : StableSys X) where

    open Cat X
    open StableSys X M
    open import Categories.Isos X
    open import Categories.Pullbacks X
    open import Categories.Monos X
    open import Categories.Pullbacks.PullbacksLemmas X
    open import Categories.Pullbacks.PastingLemmas X

    record Span (A B : Obj) : Set where
      field A' : Obj
            mhom : Hom A' A
            fhom : Hom A' B
            m∈ : ∈ mhom

    postulate quotient : ∀{A B}(mf m'f' : Span A B) → 
                         (s : Hom (Span.A' mf) (Span.A' m'f')) → 
                         Iso s → 
                         comp (Span.mhom m'f') s ≅ (Span.mhom mf) →
                         comp (Span.fhom m'f') s ≅ (Span.fhom mf) → 
                         mf ≅ m'f'

    idspan : {X : Obj} → Span X X
    idspan = record { 
      A' = _; 
      mhom = iden;
      fhom = iden;
      m∈ = iso idiso}

    compspan : {X Y Z : Obj} → Span Y Z → Span X Y → Span X Z
    compspan m'f' mf = 
      let open Pullback
          open Square
          open Span
          x = pul (fhom mf) (m∈ m'f')
          y = sq (proj₁ x)
      in record {
        A' = W y; 
        mhom = comp (mhom mf) (h y); 
        fhom = comp (fhom m'f') (k y); 
        m∈ = com (proj₂ x) (m∈ mf)}

    .idlspan : {X Y : Obj} {mf : Span X Y} → compspan idspan mf ≅ mf
    idlspan {mf = mf} =                    
      let open Pullback
          open Square
          open Span mf
      in quotient
        _ 
        mf 
        (h (sq (proj₁ (pul fhom  (iso idiso))))) 
        (pullbackiso (trivialpul fhom) 
                     (proj₁ (pul fhom 
                                 (iso idiso)))) 
        refl
        (scom (sq (proj₁ (pul fhom
                              (iso idiso)))))

    .idrspan : {X Y : Obj} {mf : Span X Y} → compspan mf idspan ≅ mf
    idrspan {mf = mf} =
      let open Pullback
          open Square
          open Span mf
      in quotient
      _ 
      mf 
      (k (sq (proj₁ (pul iden m∈)))) 
      (pullbackiso (sympul (trivialpul mhom))
                   (proj₁ (pul iden m∈)))
      (sym (scom (sq (proj₁ (pul iden m∈))))) 
      refl

    .assspan : {W X Y Z : Obj} {m''f'' : Span Y Z} {m'f' : Span X Y} {mf : Span W X} →
              compspan (compspan m''f'' m'f') mf ≅ compspan m''f'' (compspan m'f' mf)
    assspan {m''f'' = m''f''} {m'f' = m'f'} {mf = mf} = 
      let open Span mf renaming (mhom to m; fhom to f)
          open Span m'f' renaming (mhom to m'; 
                                   fhom to f'; 
                                   m∈ to m'∈)
          open Span m''f'' renaming (mhom to m'';
                                     fhom to f'';
                                     m∈ to m''∈)

          bpul : Pullback f m'
          bpul = proj₁ (pul f m'∈)

          open Pullback bpul
          open Square sq renaming (W to B)

          b'pul : Pullback (comp f' k) m''
          b'pul = proj₁ (pul (comp f' k) m''∈)

          open Pullback b'pul renaming (sq to sq'; prop to prop')
          open Square sq' renaming (W to B'; 
                                    h to h'; 
                                    k to k'; 
                                    scom to scom')

          b''pul : Pullback f' m''
          b''pul = proj₁ (pul f' m''∈)

          open Pullback b''pul renaming (sq to sq''; prop to prop'')
          open Square sq'' renaming (W to B'';
                                     h to h'';
                                     k to k'';
                                     scom to scom'')

          b'''pul : Pullback f (comp m' h'')
          b'''pul = proj₁ (pul f (com (proj₂ (pul f' m''∈)) m'∈))

          open Pullback b'''pul renaming (sq to sq''';
                                          prop to prop''')
          open Square sq''' renaming (W to B'''; 
                                      h to h'''; 
                                      k to k'''; 
                                      scom to scom''')

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
          pu = fst (prop'' sqb')

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
          pu' = fst (prop sqb''')

          open PMap pu' renaming (mor to u'; 
                                  prop1 to prop1'; 
                                  prop2 to prop2')

          upul : Pullback k h''
          upul = lem2 b'pul b''pul u (sym prop1) (sym prop2)

          u'pul : Pullback k h''
          u'pul = sympul (lem2 (sympul b'''pul) 
                               (sympul bpul) 
                               u'
                               (sym prop2')
                               (sym prop1'))

          open Pullback upul renaming (sq to usq ; prop to uprop)
          open Pullback u'pul renaming (sq to u'sq ; prop to u'prop)

          pα : PMap u'sq usq
          pα = fst (uprop u'sq)

          open PMap pα renaming (mor to α; 
                                 prop1 to prop1α; 
                                 prop2 to prop2α)

      in quotient
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
         ∎)    

    Par : Cat
    Par = record {
      Obj = Obj;
      Hom = Span;
      iden = idspan;                
      comp = compspan;
      idl = λ {X}{Y}{mf} → idlspan {mf = mf};
      idr = λ {X}{Y}{mf} → idrspan {mf = mf};
      ass = λ {_}{_}{_}{_}{m''f''}{m'f'}{mf} →  assspan {m''f'' = m''f''}
                                                        {m'f' = m'f'}
                                                        {mf = mf}}
