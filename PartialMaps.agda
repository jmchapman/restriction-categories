
open import Categories
open import Stable
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Utilities
open import Data.Product
open import Function
open import Quotients

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

    data _~Span~_ {A B}(mf m'f' : Span A B) : Set where
      spaneq : (s : Hom (Span.A' mf) (Span.A' m'f')) → 
               Iso s → 
               .(comp (Span.mhom m'f') s ≅ (Span.mhom mf)) →
               .(comp (Span.fhom m'f') s ≅ (Span.fhom mf)) → 
               mf ~Span~ m'f'

    ~refl : ∀{A B}{mf : Span A B} → mf ~Span~ mf
    ~refl {A}{B}{mf} = 
      let open Span mf renaming (mhom to m; fhom to f) 
      in spaneq iden 
                idiso 
                idr
                idr

    ~sym : ∀{A B}{mf m'f' : Span A B} → mf ~Span~ m'f' → m'f' ~Span~ mf
    ~sym {A}{B}{mf}{m'f'} (spaneq s (inv ,, rinv ,, linv) q r) = 
      let open Span mf renaming (mhom to m; fhom to f)
          open Span m'f' renaming (mhom to m'; fhom to f')
      in spaneq 
        inv 
        (s ,, linv ,, rinv) 
        (proof 
         comp m inv 
         ≅⟨ cong (λ x → comp x inv) (sym q) ⟩ 
         comp (comp m' s) inv 
         ≅⟨ ass ⟩ 
         comp m' (comp s inv)
         ≅⟨ cong (comp m') rinv ⟩ 
         comp m' iden
         ≅⟨ idr ⟩ 
         m' ∎) 
        (proof 
         comp f inv 
         ≅⟨ cong (λ x → comp x inv) (sym r) ⟩ 
         comp (comp f' s) inv 
         ≅⟨ ass ⟩ 
         comp f' (comp s inv)
         ≅⟨ cong (comp f') rinv ⟩ 
         comp f' iden
         ≅⟨ idr ⟩ 
         f' ∎) 

    ~trans : ∀{A B}{mf m'f' m''f'' : Span A B} → 
              mf ~Span~ m'f' → m'f' ~Span~ m''f'' → mf ~Span~ m''f''
    ~trans {A}{B}{mf}{m'f'}{m''f''} (spaneq s iso p q) (spaneq s' iso' p' q') =
      let open Span mf renaming (mhom to m; fhom to f)
          open Span m'f' renaming (mhom to m'; fhom to f')
          open Span m''f'' renaming (mhom to m''; fhom to f'')
          open Iso iso renaming (inv to invs; rinv to rinvs; linv to linvs)
          open Iso iso' renaming (inv to invs'; rinv to rinvs'; linv to linvs')
      in spaneq 
        (comp s' s) 
        (comp invs invs' 
         ,, 
         (proof 
          comp (comp s' s) (comp invs invs') 
          ≅⟨ ass ⟩ 
          comp s' (comp s (comp invs invs'))
          ≅⟨ cong (comp s') (sym ass) ⟩ 
          comp s' (comp (comp s invs) invs')
          ≅⟨ cong (λ x → comp s' (comp x invs')) rinvs ⟩ 
          comp s' (comp iden invs')
          ≅⟨ cong (comp s') idl ⟩ 
          comp s' invs'
          ≅⟨ rinvs' ⟩ 
          iden ∎)
         ,, 
         (proof 
          comp (comp invs invs') (comp s' s) 
          ≅⟨ ass ⟩ 
          comp invs (comp invs' (comp s' s))
          ≅⟨ cong (comp invs) (sym ass) ⟩ 
          comp invs (comp (comp invs' s') s)
          ≅⟨ cong (λ x → comp invs (comp x s)) linvs' ⟩ 
          comp invs (comp iden s)
          ≅⟨ cong (comp invs) idl ⟩ 
          comp invs s
          ≅⟨ linvs ⟩ 
          iden ∎))
        (proof 
         comp m'' (comp s' s) 
         ≅⟨ sym ass ⟩ 
         comp (comp m'' s') s
         ≅⟨ cong (λ x → comp x s) p' ⟩ 
         comp m' s
         ≅⟨ p ⟩ 
         m ∎)
        (proof 
         comp f'' (comp s' s) 
         ≅⟨ sym ass ⟩ 
         comp (comp f'' s') s
         ≅⟨ cong (λ x → comp x s) q' ⟩ 
         comp f' s
         ≅⟨ q ⟩ 
         f ∎)

    Span~EqR : ∀{A B} → EqR (Span A B)
    Span~EqR = record { 
      _~_    = _~Span~_; 
      ~refl  = ~refl; 
      ~sym   = ~sym; 
      ~trans = ~trans }

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

{-
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
-}
 
    .idlspan : {X Y : Obj} {mf : Span X Y} → compspan idspan mf ~Span~ mf
    idlspan {X}{Y}{mf} = 
      let open Pullback
          open Square
          open Span mf
      in spaneq 
      (h (sq (proj₁ (pul fhom (iso idiso))))) 
      (pullbackiso (trivialpul fhom) 
                     (proj₁ (pul fhom 
                                 (iso idiso)))) 
      refl 
      (scom (sq (proj₁ (pul fhom (iso idiso)))))

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


  
    open Quotient
    Par : Cat
    Par = record {
      Obj = Obj;
      Hom = λ A B → Q (quot (Span A B) (Span~EqR));
      iden = λ {A} → abs (quot (Span A A) (Span~EqR)) idspan; --idspan;                
      comp = λ {A} {B} {C} f g → abs (quot (Span A C) Span~EqR) 
                                     (compspan (rep (quot (Span B C) Span~EqR) f) 
                                               (rep (quot (Span A B) Span~EqR) g)); -- compspan;
      idl = λ {A}{B}{mf} → trans (ax1 (quot (Span A B) Span~EqR) 
                                      _ 
                                      _ 
                                      {!idlspan {mf = rep (quot (Span A B) Span~EqR) mf}!}) 
                                 (ax2 (quot (Span A B) Span~EqR) mf);
{-
trans (ax1 (quot (Span A B) Span~EqR) 
                                      (rep (quot (Span A B) Span~EqR) mf) 
                                      {!!} 
                                      {!idlspan {mf = rep (quot (Span A B) Span~EqR) mf}!}) 
                                 (ax2 (quot (Span A B) Span~EqR) mf); 
-}
          -- λ {X}{Y}{mf} → idlspan {mf = mf};
      idr = {!!}; -- λ {X}{Y}{mf} → idrspan {mf = mf};
      ass = {!!}} -- λ {_}{_}{_}{_}{m''f''}{m'f'}{mf} →  assspan {m''f'' = m''f''}
              --                                          {m'f' = m'f'}
              --                                          {mf = mf}}
