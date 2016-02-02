{-# OPTIONS --type-in-type #-}
open import Categories
open import PartialMaps.Stable
open import Utilities

module PartialMaps.Cat (X : Cat)(M : StableSys X) where

open Cat X
open StableSys X M
open import Categories.Isos X
open import Categories.Pullbacks X
open import Categories.Monos X
open import Categories.Pullbacks.PastingLemmas X

record Span (A B : Obj) : Set where
  constructor span
  field A'    : Obj
        mhom  : Hom A' A
        fhom  : Hom A' B
        m∈sys : ∈sys mhom

record _~Span~_ {A B}(mf ng : Span A B) : Set where
  constructor spaneq 
  field s       : Hom (Span.A' mf) (Span.A' ng)
        sIso    : Iso s
        leftTr  : comp (Span.mhom ng) s ≅ (Span.mhom mf)
        rightTr : comp (Span.fhom ng) s ≅ (Span.fhom mf)

~refl : ∀{A B}{mf : Span A B} → mf ~Span~ mf
~refl = spaneq iden idIso idr idr

~sym : ∀{A B}{mf m'f' : Span A B} → mf ~Span~ m'f' → m'f' ~Span~ mf
~sym {mf = span _ m f _}{span _ m' f' _} (spaneq s (iso inv rinv linv) q r) = 
  spaneq 
    inv 
    (iso s linv rinv) 
    (proof 
     comp m inv 
     ≅⟨ cong (λ x → comp x inv) (sym q) ⟩ 
     comp (comp m' s) inv 
     ≅⟨ ass ⟩ 
     comp m' (comp s inv)
     ≅⟨ cong (comp m') rinv ⟩ 
     comp m' iden
     ≅⟨ idr ⟩ 
     m' 
     ∎) 
    (proof 
     comp f inv 
     ≅⟨ cong (λ x → comp x inv) (sym r) ⟩ 
     comp (comp f' s) inv 
     ≅⟨ ass ⟩ 
     comp f' (comp s inv)
     ≅⟨ cong (comp f') rinv ⟩ 
     comp f' iden
     ≅⟨ idr ⟩ 
     f' 
     ∎) 

~trans : ∀{A B}{mf m'f' m''f'' : Span A B} → 
          mf ~Span~ m'f' → m'f' ~Span~ m''f'' → mf ~Span~ m''f''
~trans {mf = span _ m f _}{span _ m' f' _}{span _ m'' f'' _} 
       (spaneq s (iso invs rinvs linvs) p q) (spaneq s' (iso invs' rinvs' linvs') p' q') =
  spaneq 
    (comp s' s) 
    (iso (comp invs invs')
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
          iden 
          ∎)
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
          iden 
          ∎))
    (proof 
     comp m'' (comp s' s) 
     ≅⟨ sym ass ⟩ 
     comp (comp m'' s') s
     ≅⟨ cong (λ x → comp x s) p' ⟩ 
     comp m' s
     ≅⟨ p ⟩ 
     m 
     ∎)
    (proof 
     comp f'' (comp s' s) 
     ≅⟨ sym ass ⟩ 
     comp (comp f'' s') s
     ≅⟨ cong (λ x → comp x s) q' ⟩ 
     comp f' s
     ≅⟨ q ⟩ 
     f 
     ∎)

Span~EqR : ∀{A B} → EqR (Span A B)
Span~EqR = 
  _~Span~_ ,
  record { 
    refl  = ~refl; 
    sym   = ~sym; 
    trans = ~trans }

idSpan : {X : Obj} → Span X X
idSpan = span _ iden iden (iso∈sys idIso)

compSpan : {X Y Z : Obj} → Span Y Z → Span X Y → Span X Z
compSpan (span B' n g n∈) (span A' m f m∈) = 
  let p , h∈ = pul∈sys f n∈
      pullback (square W h k _) _ = p
  in span W (comp m h) (comp g k) (comp∈sys h∈ m∈)

∼cong : {X Y Z : Obj}{mf m'f' : Span Y Z} → mf ~Span~ m'f' → 
                     {ng n'g' : Span X Y} → ng ~Span~ n'g' → 
                     compSpan mf ng ~Span~ compSpan m'f' n'g'
∼cong {mf = span _ m f m∈}{span _ m' f' m'∈} (spaneq s (iso invs rinv linv) ltri rtri)
      {span _ n g n∈}{span _ n' g' n'∈} (spaneq s' (iso invs' rinv' linv') ltri' rtri') = 
  let pullback (square W h k scom) uniqPul , h∈ = pul∈sys g m∈
      p' , h'∈ = pul∈sys g' m'∈
      pullback (square W' h' k' scom') uniqPul' = p'

      hexcom : comp g' (comp s' h) ≅ comp m' (comp s k) 
      hexcom = 
        proof 
        comp g' (comp s' h) 
        ≅⟨ sym ass ⟩ 
        comp (comp g' s') h
        ≅⟨ cong (λ x → comp x h) rtri' ⟩ 
        comp g h
        ≅⟨ scom ⟩ 
        comp m k 
        ≅⟨ cong (λ x → comp x k) (sym ltri) ⟩ 
        comp (comp m' s) k 
        ≅⟨ ass ⟩ 
        comp m' (comp s k) 
        ∎

      hexsq : Square g' m'
      hexsq = record { 
        W = W; 
        h = comp s' h; 
        k = comp s k; 
        scom = hexcom }

      hexpul : Pullback g' m'
      hexpul = record { 
        sq   = hexsq; 
        uniqPul = λ {(square W'' h'' k'' scom'') → 
          let invrtri' : comp g invs' ≅ g'
              invrtri' = proof 
                comp g invs' 
                ≅⟨ cong (λ x → comp x invs') (sym rtri') ⟩  
                comp (comp g' s') invs' 
                ≅⟨ ass ⟩  
                comp g' (comp s' invs')
                ≅⟨ cong (comp g') rinv' ⟩  
                comp g' iden
                ≅⟨ idr ⟩  
                g' 
                ∎
                
              invltri : m' ≅ comp m invs
              invltri = proof 
                m' 
                ≅⟨ sym idr ⟩ 
                comp m' iden
                ≅⟨ cong (comp m') (sym rinv) ⟩ 
                comp m' (comp s invs)
                ≅⟨ sym ass ⟩ 
                comp (comp m' s) invs 
                ≅⟨ cong (λ x → comp x invs) ltri ⟩ 
                comp m invs 
                ∎

              scom''' : comp g (comp invs' h'') ≅ comp m (comp invs k'') 
              scom''' = 
                proof 
                comp g (comp invs' h'') 
                ≅⟨ sym ass ⟩ 
                comp (comp g invs') h''
                ≅⟨ cong (λ x → comp x h'') invrtri' ⟩ 
                comp g' h''
                ≅⟨ scom'' ⟩ 
                comp m' k''
                ≅⟨ cong (λ x → comp x k'') invltri ⟩ 
                comp (comp m invs) k''
                ≅⟨ ass ⟩ 
                comp m (comp invs k'') 
                ∎
                
              sq'' : Square g m
              sq'' = square W'' (comp invs' h'') (comp invs k'') scom'''

              sqmap u' leftTr rightTr , pu' = uniqPul sq''

              leftTr' : comp (comp s' h) u' ≅ h''
              leftTr' = proof 
                comp (comp s' h) u' 
                ≅⟨ ass ⟩ 
                comp s' (comp h u')
                ≅⟨ cong (comp s') leftTr ⟩ 
                comp s' (comp invs' h'')
                ≅⟨ sym ass ⟩ 
                comp (comp s' invs') h''
                ≅⟨ cong (λ x → comp x h'') rinv' ⟩ 
                comp iden h''
                ≅⟨ idl ⟩ 
                h'' 
                ∎ 

              rightTr' : comp (comp s k) u' ≅ k''
              rightTr' = proof 
                comp (comp s k) u' 
                ≅⟨ ass ⟩ 
                comp s (comp k u')
                ≅⟨ cong (comp s) rightTr ⟩ 
                comp s (comp invs k'')
                ≅⟨ sym ass ⟩ 
                comp (comp s invs) k''
                ≅⟨ cong (λ x → comp x k'') rinv ⟩ 
                comp iden k''
                ≅⟨ idl ⟩ 
                k'' 
                ∎
          in record { sqMor = u'; leftTr = leftTr'; rightTr = rightTr' }
            , 
            (λ {(sqmap u'' leftTr'' rightTr'') →
              let leftTr''' : comp h u'' ≅ comp invs' h''
                  leftTr''' = 
                    proof 
                    comp h u'' 
                    ≅⟨ sym idl ⟩ 
                    comp iden (comp h u'' )
                    ≅⟨ cong (λ x → comp x (comp h u'')) (sym linv') ⟩ 
                    comp (comp invs' s') (comp h u'' )
                    ≅⟨ ass ⟩ 
                    comp invs' (comp s' (comp h u''))
                    ≅⟨ cong (comp invs') (sym ass) ⟩ 
                    comp invs' (comp (comp s' h) u'') 
                    ≅⟨ cong (comp invs') leftTr'' ⟩ 
                    comp invs' h'' 
                    ∎

                  rightTr''' : comp k u'' ≅ comp invs k''
                  rightTr''' = 
                    proof
                    comp k u'' 
                    ≅⟨ sym idl ⟩
                    comp iden (comp k u'')
                    ≅⟨ cong (λ x → comp x (comp k u'')) (sym linv) ⟩
                    comp (comp invs s) (comp k u'')
                    ≅⟨ ass ⟩
                    comp invs (comp s (comp k u''))
                    ≅⟨ cong (comp invs) (sym ass) ⟩
                    comp invs (comp (comp s k) u'')
                    ≅⟨ cong (comp invs) rightTr'' ⟩
                    comp invs k''
                    ∎
              in pu' (sqmap u'' leftTr''' rightTr''')})} }

      i = pullbackIso p' hexpul
      sqmap u p1 p2 = proj₁ (uniqPul' hexsq)

      t1 : comp (comp n' h') u ≅ comp n h
      t1 = 
        proof 
        comp (comp n' h') u 
        ≅⟨ ass ⟩ 
        comp n' (comp h' u)
        ≅⟨ cong (comp n') p1 ⟩ 
        comp n' (comp s' h)
        ≅⟨ sym ass ⟩ 
        comp (comp n' s') h
        ≅⟨ cong (λ x → comp x h) ltri' ⟩ 
        comp n h 
        ∎

      t2 : comp (comp f' k') u ≅ comp f k
      t2 = 
        proof 
        comp (comp f' k') u
        ≅⟨ ass ⟩ 
        comp f' (comp k' u)
        ≅⟨ cong (comp f') p2 ⟩ 
        comp f' (comp s k)
        ≅⟨ sym ass ⟩ 
        comp (comp f' s) k
        ≅⟨ cong (λ x → comp x k) rtri ⟩ 
        comp f k 
        ∎
  in spaneq u i t1 t2

-- shorthands

qspan : ∀ A B → Quotient (Span A B) Span~EqR
qspan A B = quot (Span A B) Span~EqR

QSpan : ∀ A B → Set
QSpan A B = Quotient.Q (qspan A B)

abs : {A B : Obj} → Span A B → QSpan A B
abs {A}{B} = Quotient.abs (qspan A B)

compat : ∀{A B}(C : QSpan A B → Set) → 
         ((mf : Span A B) → C (abs mf)) → Set
compat {A}{B} = Quotient.compat (qspan A B)

qelim : ∀{A B}(C : QSpan A B → Set)
        (f : (mf : Span A B) → C (abs mf)) → 
        compat C f → (x : QSpan A B) → C x
qelim {A}{B} = Quotient.qelim (qspan A B)

lift : ∀{A B C}(f : Span A B → C) → compat (λ _ → C) f → 
       QSpan A B → C
lift {A}{B} = QuotientLib.lift (qspan A B)

sound : ∀{A B}{mf ng : Span A B} → 
         mf ~Span~ ng → abs mf ≅ abs ng
sound {A}{B} = Quotient.sound (qspan A B)

qbeta : ∀{A B}(C : QSpan A B → Set)
         (f : (mf : Span A B) → C (abs mf))
         (p : compat C f)(mf : Span A B) → 
         qelim C f p (abs mf) ≅ f mf
qbeta {A}{B} = Quotient.qbeta (qspan A B)

compat₂ : ∀{A B A' B'}(C : QSpan A B → QSpan A' B' → Set) → 
          (f : (mf : Span A B)(ng : Span A' B') → 
               C (abs mf) (abs ng)) → Set
compat₂ {A}{B}{A'}{B'} = Quotient₂Lib.compat₂ (qspan A B) (qspan A' B')

qelim₂ : ∀{A B A' B'}(C : QSpan A B → QSpan A' B' → Set)
         (f : (mf : Span A B)(ng : Span A' B') → 
              C (abs mf) (abs ng)) → 
         compat₂ C f → (x : QSpan A B)(x' : QSpan A' B') → C x x'
qelim₂ {A}{B}{A'}{B'} = Quotient₂Lib.qelim₂ (qspan A B) (qspan A' B')

lift₂ : ∀{A B A' B' C}(f : Span A B → Span A' B' → C) → 
        compat₂ (λ _ _ → C) f → QSpan A B → QSpan A' B' → C
lift₂ {A}{B}{A'}{B'} = Quotient₂Lib.lift₂ (qspan A B ) (qspan A' B')

qbeta₂ : ∀{A B A' B'}(C : QSpan A B → QSpan A' B' → Set)
         (f : (mf : Span A B)(ng : Span A' B') → 
              C (abs mf) (abs ng))
         (p : compat₂ C f)(mf : Span A B)(ng : Span A' B') → 
         qelim₂ C f p (abs mf) (abs ng) ≅ f mf ng
qbeta₂ {A}{B}{A'}{B'} = Quotient₂Lib.qbeta₂ (qspan A B) (qspan A' B')

compat₃ : ∀{A B A' B' A'' B''}
          (C : QSpan A B → QSpan A' B' → QSpan A'' B'' → Set)
          (f : (mf : Span A B)(ng : Span A' B')(lh : Span A'' B'') → 
                C (abs mf) (abs ng) (abs lh)) → Set
compat₃ {A}{B}{A'}{B'}{A''}{B''} = 
  Quotient₃Lib.compat₃ (qspan A B) (qspan A' B') (qspan A'' B'')

qelim₃ : ∀{A B A' B' A'' B''}
         (C : QSpan A B → QSpan A' B' → QSpan A'' B'' → Set)
         (f : (mf : Span A B)(ng : Span A' B')(lh : Span A'' B'') → 
              C (abs mf) (abs ng) (abs lh)) → 
         compat₃ C f → 
         (x : QSpan A B)(x' : QSpan A' B')(x'' : QSpan A'' B'') → 
         C x x' x''
qelim₃ {A}{B}{A'}{B'}{A''}{B''} = 
  Quotient₃Lib.qelim₃ (qspan A B) (qspan A' B') (qspan A'' B'')

qcompSpan : ∀{A B C} → QSpan B C → QSpan A B → QSpan A C
qcompSpan = lift₂ (λ x y → abs (compSpan x y)) (λ p q → sound (∼cong p q))

idlSpan : ∀{A B}{mf : Span A B} → compSpan idSpan mf ~Span~ mf
idlSpan {mf = span _ _ f _} = 
  let p , _ = pul∈sys f (iso∈sys idIso)
      pullback (square _ h _ scom) _ = p
  in spaneq h (pullbackIso (trivialPullback f) p) refl scom

qcompSpanQbeta : ∀{A B C}{ng : Span B C}{mf : Span A B} → 
                 qcompSpan (abs ng) (abs mf) ≅ abs (compSpan ng mf)
qcompSpanQbeta = qbeta₂ _ (λ x y → abs (compSpan x y)) (λ p q → sound (∼cong p q)) _ _

qidlSpan : ∀{A B}{x : QSpan A B} → qcompSpan (abs idSpan) x ≅ x
qidlSpan = 
  qelim (λ z → qcompSpan (abs idSpan) z ≅ z)
        (λ mf → 
          proof
          qcompSpan (abs idSpan) (abs mf)
          ≅⟨ qcompSpanQbeta ⟩
          abs (compSpan idSpan mf)
          ≅⟨ sound idlSpan ⟩
          abs mf
          ∎) 
        (hirR ∘ sound)
        _

idrSpan : {X Y : Obj} {mf : Span X Y} → compSpan mf idSpan ~Span~ mf
idrSpan {mf = span _ m _ m∈} =
  let p , _ = pul∈sys iden m∈
      pullback (square _ _ k scom) _ = p
  in spaneq k (pullbackIso (symPullback (trivialPullback m)) p) (sym scom) refl

qidrSpan : ∀{A B}{x : QSpan A B} → qcompSpan x (abs idSpan) ≅ x
qidrSpan = 
  qelim (λ z → qcompSpan z (abs idSpan) ≅ z)
        (λ mf → 
          proof
          qcompSpan (abs mf) (abs idSpan)
          ≅⟨ qcompSpanQbeta ⟩
          abs (compSpan mf idSpan)
          ≅⟨ sound idrSpan ⟩
          abs mf
          ∎) 
        (hirR ∘ sound)
        _

assSpan : {W X Y Z : Obj} 
          {m''f'' : Span Y Z} {m'f' : Span X Y} {mf : Span W X} →
          compSpan (compSpan m''f'' m'f') mf ~Span~ 
          compSpan m''f'' (compSpan m'f' mf)
assSpan {m''f'' = span _ m'' f'' m''∈}{span _ m' f' m'∈}{span _ m f m∈} = 
    let bpul : Pullback f m'
        bpul = proj₁ (pul∈sys f m'∈)

        open Pullback bpul
        open Square sq renaming (W to B)

        b'pul : Pullback (comp f' k) m''
        b'pul = proj₁ (pul∈sys (comp f' k) m''∈)

        open Pullback b'pul renaming (sq to sq'; uniqPul to uniqPul')
        open Square sq' renaming (W to B'; 
                                  h to h'; 
                                  k to k'; 
                                  scom to scom')

        b''pul : Pullback f' m''
        b''pul = proj₁ (pul∈sys f' m''∈)

        open Pullback b''pul renaming (sq to sq''; uniqPul to uniqPul'')
        open Square sq'' renaming (W to B'';
                                   h to h'';
                                   k to k'';
                                   scom to scom'')

        b'''pul : Pullback f (comp m' h'')
        b'''pul = proj₁ (pul∈sys f (comp∈sys (proj₂ (pul∈sys f' m''∈)) m'∈))

        open Pullback b'''pul renaming (sq to sq''';
                                        uniqPul to uniqPul''')
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

        pu : SqMap sqb' sq''
        pu = proj₁ (uniqPul'' sqb')

        open SqMap pu renaming (sqMor to u)

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

        pu' : SqMap sqb''' sq
        pu' = proj₁ (uniqPul sqb''')

        open SqMap pu' renaming (sqMor to u'; 
                                leftTr to leftTr'; 
                                rightTr to rightTr')

        upul : Pullback k h''
        upul = pasting2 b'pul b''pul u (sym leftTr) (sym rightTr)

        u'pul : Pullback k h''
        u'pul = symPullback (pasting2 (symPullback b'''pul) 
                                      (symPullback bpul) 
                                      u'
                                      (sym rightTr')
                                      (sym leftTr'))

        open Pullback upul renaming (sq to usq ; uniqPul to uprop)
        open Pullback u'pul renaming (sq to u'sq ; uniqPul to u'prop)

        pα : SqMap u'sq usq
        pα = proj₁ (uprop u'sq)

        open SqMap pα renaming (sqMor to α; 
                               leftTr to leftTrα; 
                               rightTr to rightTrα)
    in spaneq
      α 
      (pullbackIso upul u'pul) 
      (proof 
       comp (comp (comp m h) h') α 
       ≅⟨ ass ⟩ 
       comp (comp m h) (comp h' α)
       ≅⟨ cong (comp (comp m h)) leftTrα ⟩ 
       comp (comp m h) u'
       ≅⟨ ass ⟩ 
       comp m (comp h u')
       ≅⟨ cong (comp m) leftTr' ⟩ 
       comp m h'''
       ∎) 
      (proof 
       comp (comp f'' k') α
       ≅⟨ cong (λ y → comp (comp f'' y) α) (sym rightTr) ⟩ 
       comp (comp f'' (comp k'' u)) α 
       ≅⟨ cong (λ y → comp y α) (sym ass) ⟩ 
       comp (comp (comp f'' k'') u) α
       ≅⟨ ass ⟩ 
       comp (comp f'' k'') (comp u α)
       ≅⟨ cong (comp (comp f'' k'')) rightTrα ⟩ 
       comp (comp f'' k'') k'''
       ∎)    

qassSpan : ∀{A B C D}{x : QSpan C D}{y : QSpan B C}{z : QSpan A B} → 
           qcompSpan (qcompSpan x y) z ≅ qcompSpan x (qcompSpan y z)
qassSpan = 
  qelim₃ (λ x y z → qcompSpan (qcompSpan x y) z ≅ qcompSpan x (qcompSpan y z))
         (λ mf ng lh → 
           proof
           qcompSpan (qcompSpan (abs mf) (abs ng)) (abs lh)
           ≅⟨ cong (λ z → qcompSpan z (abs lh)) qcompSpanQbeta ⟩
           qcompSpan (abs (compSpan mf ng)) (abs lh)
           ≅⟨ qcompSpanQbeta ⟩
           abs (compSpan (compSpan mf ng) lh)
           ≅⟨ sound assSpan ⟩
           abs (compSpan mf (compSpan ng lh))
           ≅⟨ sym qcompSpanQbeta ⟩
           qcompSpan (abs mf) (abs (compSpan ng lh))
           ≅⟨ cong (qcompSpan (abs mf)) (sym qcompSpanQbeta) ⟩
           qcompSpan (abs mf) (qcompSpan (abs ng) (abs lh))
           ∎) 
         (λ p r s → 
           hirR (cong₃ (λ x y z → qcompSpan x (qcompSpan y z))
                       (sound p) (sound r) (sound s))) 
         _ _ _

Par : Cat
Par = record {
  Obj  = Obj;
  Hom  = QSpan;
  iden = abs idSpan;
  comp = qcompSpan;
  idl  = qidlSpan;
  idr  = qidrSpan;
  ass  = qassSpan}

