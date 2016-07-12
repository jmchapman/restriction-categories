
open import Categories
open import PartialMaps.Stable

module Soundness {i j}(X : Cat {i}{j}) (M : StableSys X) where

open import Utilities
open import Restriction.Cat
open import PartialMaps.Cat X M
open Cat X
open import Categories.Pullbacks X
open StableSys X M
open import Categories.Pullbacks.PastingLemmas X
open import Categories.Isos X

restSpan : ∀{A B} → Span A B → Span A A
restSpan (span A' mhom fhom m∈) = span A' mhom mhom m∈

~congRestSpan : ∀{A B}{mf m'f' : Span A B} → mf ~Span~ m'f' → 
                restSpan mf ~Span~ restSpan m'f'
~congRestSpan (spaneq s i q r) = spaneq s i q q

qrestSpan : ∀{A B} → QSpan A B → QSpan A A
qrestSpan = lift _ (abs ∘ restSpan) (sound ∘ ~congRestSpan)

R1Span : ∀{A B}{mf : Span A B} → compSpan mf (restSpan mf) ~Span~ mf
R1Span {mf = span _ m f m∈} =
  let p , _ = pul∈sys m m∈
      pullback (square _ h _ scom) _ = p
  in spaneq h
            (pullbackIso (monicPullback (mono∈sys m∈)) p)
            refl
            (cong (comp f) (mono∈sys m∈ scom))

R2Span : ∀{A B C}{mf : Span A B}{m'f' : Span A C} → 
          compSpan (restSpan mf) (restSpan m'f') ~Span~ compSpan (restSpan m'f') (restSpan mf)
R2Span {mf = span _ m f m∈} {span _ m' f' m'∈} = 
  let p , _ = pul∈sys m' m∈
      pullback sq _ = symPullback p
      square _ h k scom = sq
      p' , _ = pul∈sys m m'∈
      pullback sq' uniqPul' = p'
      square _ h' k' scom' = sq'
      sqmap u leftTr rightTr  , _ = uniqPul' sq
  in spaneq u 
            (pullbackIso p' (symPullback p)) 
            (proof
             comp (comp m h') u 
             ≅⟨ ass ⟩
             comp m (comp h' u) 
             ≅⟨ cong (comp m) leftTr ⟩
             comp m h 
             ≅⟨ scom ⟩ 
             comp m' k 
             ∎) 
            (proof
             comp (comp m' k') u 
             ≅⟨ ass ⟩
             comp m' (comp k' u) 
             ≅⟨ cong (comp m') rightTr ⟩
             comp m' k 
             ≅⟨ sym scom ⟩ 
             comp m h 
             ∎)

R3Span : ∀{A B C}{mf : Span A B}{m'f' : Span A C} →
          compSpan (restSpan m'f') (restSpan mf) ~Span~ restSpan (compSpan m'f' (restSpan mf))
R3Span {mf = span _ m f m∈} {span _ m' f' m'∈} = 
  let pullback (square _ h k scom) _ , _ = pul∈sys m m'∈
  in spaneq
    iden 
    idIso 
    idr
    (proof 
     comp (comp m h) iden 
     ≅⟨ idr ⟩ 
     comp m h 
     ≅⟨ scom ⟩ 
     comp m' k 
     ∎)

R4Span : ∀{A B C}{mf : Span A B}{m'f' : Span B C} →
          compSpan (restSpan m'f') mf ~Span~ compSpan mf (restSpan (compSpan m'f' mf))
R4Span {mf = span _ m f m∈} {span _ m' f' m'∈} = 
  let pullback (square _ h k scom) uniqPul , _ = pul∈sys f m'∈
      p'' = pasting1 (monicPullback (mono∈sys m∈)) (trivialPullback h)
      pullback sq'' _ = p''
      p' , _ = pul∈sys (comp m h) m∈
      pullback sq' uniqPul' = p'
      square _ h' k' scom' = sq'
      sqmap u leftTr rightTr , _ = uniqPul' sq'' 
  in spaneq 
    u 
    (pullbackIso p' p'') 
    (proof 
     comp (comp (comp m h) h') u 
     ≅⟨ ass ⟩ 
     comp (comp m h) (comp h' u) 
     ≅⟨ cong (comp (comp m h)) leftTr  ⟩ 
     comp (comp m h) iden 
     ≅⟨ idr ⟩ 
     comp m h 
     ∎) 
    (proof
     comp (comp f k') u
     ≅⟨ ass ⟩
     comp f (comp k' u)
     ≅⟨ cong (comp f) rightTr ⟩
     comp f (comp iden h)
     ≅⟨ cong (comp f) idl ⟩
     comp f h
     ≅⟨ scom ⟩
     comp m' k
     ∎)

liftbetaRest : ∀{A B}{mf : Span A B} → 
                 qrestSpan (abs mf) ≅ abs (restSpan mf)
liftbetaRest = liftbeta _ (abs ∘ restSpan) (sound ∘ ~congRestSpan) _

qR1Span : ∀{A B}{x : QSpan A B} → qcompSpan x (qrestSpan x) ≅ x
qR1Span = 
  lift (λ z → qcompSpan z (qrestSpan z) ≅ z) 
        (λ mf → 
          proof
          qcompSpan (abs mf) (qrestSpan (abs mf))
          ≅⟨ cong (qcompSpan (abs mf)) liftbetaRest ⟩
          qcompSpan (abs mf) (abs (restSpan mf))
          ≅⟨ liftbetaComp ⟩
          abs (compSpan mf (restSpan mf))
          ≅⟨ sound R1Span ⟩
          abs mf
          ∎)
        (fixtypes ∘ sound)
        _

qR2Span : ∀{A B C}{f : QSpan A B}{g : QSpan A C} → 
           qcompSpan (qrestSpan g) (qrestSpan f) ≅ 
           qcompSpan (qrestSpan f) (qrestSpan g)
qR2Span = 
  lift₂ (λ x y → qcompSpan (qrestSpan x) (qrestSpan y) ≅ 
                  qcompSpan (qrestSpan y) (qrestSpan x))
         (λ mf ng → 
            proof
            qcompSpan (qrestSpan (abs mf)) (qrestSpan (abs ng))
            ≅⟨ cong₂ qcompSpan liftbetaRest liftbetaRest ⟩
            qcompSpan (abs (restSpan mf)) (abs (restSpan ng))
            ≅⟨ liftbetaComp ⟩
            abs (compSpan (restSpan mf) (restSpan ng))
            ≅⟨ sound (R2Span {mf = mf}{ng}) ⟩
            abs (compSpan (restSpan ng) (restSpan mf))
            ≅⟨ sym liftbetaComp ⟩
            qcompSpan (abs (restSpan ng)) (abs (restSpan mf))
            ≅⟨ sym (cong₂ qcompSpan liftbetaRest liftbetaRest) ⟩
            qcompSpan (qrestSpan (abs ng)) (qrestSpan (abs mf))
            ∎)
         (λ p r → fixtypes (cong₂ (λ x y → qcompSpan (qrestSpan x) (qrestSpan y)) 
                              (sound r) (sound p)))
         _ _

qR3Span : ∀{A B C}{f : QSpan A B}{g : QSpan A C} → 
           qcompSpan (qrestSpan g) (qrestSpan f) ≅ 
           qrestSpan (qcompSpan g (qrestSpan f))
qR3Span = 
  lift₂ (λ x y → qcompSpan (qrestSpan x) (qrestSpan y) ≅ 
                  qrestSpan (qcompSpan x (qrestSpan y)))
         (λ mf ng → 
            proof
            qcompSpan (qrestSpan (abs mf)) (qrestSpan (abs ng))
            ≅⟨ cong₂ qcompSpan liftbetaRest liftbetaRest ⟩
            qcompSpan (abs (restSpan mf)) (abs (restSpan ng))
            ≅⟨ liftbetaComp ⟩
            abs (compSpan (restSpan mf) (restSpan ng))
            ≅⟨ sound (R3Span {mf = ng}{mf}) ⟩
            abs (restSpan (compSpan mf (restSpan ng)))
            ≅⟨ sym liftbetaRest ⟩
            qrestSpan (abs (compSpan mf (restSpan ng)))
            ≅⟨ cong qrestSpan (sym liftbetaComp) ⟩
            qrestSpan (qcompSpan (abs mf) (abs (restSpan ng)))
              ≅⟨ cong (qrestSpan ∘ qcompSpan (abs mf)) (sym liftbetaRest) ⟩
            qrestSpan (qcompSpan (abs mf) (qrestSpan (abs ng)))
            ∎)
         (λ p r → fixtypes (cong₂ (λ x y → qrestSpan (qcompSpan x (qrestSpan y))) 
                              (sound p) (sound r)))
         _ _

qR4Span : ∀{A B C}{f : QSpan A B}{g : QSpan B C} → 
           qcompSpan (qrestSpan g) f ≅ qcompSpan f (qrestSpan (qcompSpan g f))
qR4Span = 
  lift₂ (λ x y → qcompSpan (qrestSpan x) y ≅ 
                  qcompSpan y (qrestSpan (qcompSpan x y)))
         (λ mf ng → 
            proof
            qcompSpan (qrestSpan (abs mf)) (abs ng)
            ≅⟨ cong (λ z → qcompSpan z (abs ng)) liftbetaRest ⟩
            qcompSpan (abs (restSpan mf)) (abs ng)
            ≅⟨ liftbetaComp ⟩
            abs (compSpan (restSpan mf) ng)
            ≅⟨ sound (R4Span {mf = ng}{mf}) ⟩
            abs (compSpan ng (restSpan (compSpan mf ng)))
            ≅⟨ sym liftbetaComp ⟩
            qcompSpan (abs ng) (abs (restSpan (compSpan mf ng)))
            ≅⟨ cong (qcompSpan (abs ng)) (sym liftbetaRest) ⟩
            qcompSpan (abs ng) (qrestSpan (abs (compSpan mf ng)))
            ≅⟨ cong (qcompSpan (abs ng) ∘ qrestSpan) (sym liftbetaComp) ⟩
            qcompSpan (abs ng) (qrestSpan (qcompSpan (abs mf) (abs ng)))
            ∎)
         (λ p r → fixtypes (cong₂ (λ x y → qcompSpan y (qrestSpan (qcompSpan x y)))
                              (sound p) (sound r)))
         _ _

RestPar : RestCat
RestPar = record { 
  cat = Par; 
  rest = qrestSpan;
  R1 = qR1Span;
  R2 = qR2Span;
  R3 = qR3Span;
  R4 = qR4Span}


{-
-- every restriction in Par splits

open import Categories.Idems Par
open Categories.Isos X
open Lemmata RestPar

qrestSpanIdem : ∀{A B}(f : QSpan A B) → Idem
qrestSpanIdem f = record { E = _; e = qrestSpan f; law = lemii}

sectionSpan : ∀{A B}(f : Span A B) → Span (Span.A' f) A
sectionSpan f = 
  let open Span f
  in record { A' = A'; mhom = iden; fhom = mhom; m∈ = iso idiso }

retractionSpan : ∀{A B}(f : Span A B) → Span A (Span.A' f)
retractionSpan f = 
  let open Span f
  in record { A' = A'; mhom = mhom; fhom = iden; m∈ = m∈ }

{-
qrestSpanSplit : ∀{A B}(f : QSpan A B) → Split (qrestSpanIdem f)
qrestSpanSplit = 
  lift (Split ∘ qrestSpanIdem)
        (λ mf → let open Span mf in record { 
          B = A' ; 
          s = abs (sectionSpan mf) ; 
          r = abs (retractionSpan mf) ; 
          law1 = {!!} ; 
          law2 = {!!} })
        (λ x → {!split≅ !})
-}




{-


restSpanSplit : ∀{A B}(f : Span A B) → Split (restSpanIdem (abs f))
restSpanSplit {A}{B} f = 
  let open Span f
  in record { 
    B    = A'; 
    s    = abs (qs f);
    r    = abs (qr f);
    law1 = 
      let open Pullback (proj₁ (pul (iden {A'}) (iso idiso)))
          open Square sq
  
          myp : Pullback (iden {A'}) (iden {A'})
          myp = trivialpul (iden {A'})

          lem : h ≅ k
          lem = proof 
                h 
                ≅⟨ sym idl ⟩ 
                comp iden h
                ≅⟨ scom ⟩
                comp iden k
                ≅⟨ idl ⟩
                k 
                ∎

          lem' : compSpan (qs f) (qr f) ~Span~ restSpan f
          lem' = spaneq (PMap.mor (fst (Pullback.prop myp sq))) 
                         (pullbackiso myp (proj₁ (pul (iden {A'}) (iso idiso))))
                         refl
                         (proof 
                          comp mhom h 
                          ≅⟨ cong (comp mhom) lem ⟩ 
                          comp mhom k 
                          ∎)

      in proof
         qcomp (abs (qs f)) (abs (qr f))
         ≅⟨ qcompabsabs ⟩
         abs (compSpan (qs f) (qr f))
         ≅⟨ sound _ _ lem' ⟩
         abs (restSpan f)
         ≅⟨ sym liftbetaRest ⟩
         qrestSpan (abs f)
         ∎;
    law2 = 
      let open Pullback (proj₁ (pul mhom m∈)) 
          open Square sq
          
          myp : Pullback mhom mhom 
          myp = monic→pullback (mon m∈)
  
          lem : compSpan (qr f) (qs f) ~Span~ idSpan
          lem = spaneq (PMap.mor (fst (Pullback.prop myp sq))) 
                       (pullbackiso myp (proj₁ (pul mhom m∈))) 
                       refl 
                       (proof 
                        comp iden h 
                        ≅⟨ idl ⟩
                        h
                        ≅⟨ mon m∈ scom ⟩ 
                        k
                        ≅⟨ sym idl ⟩
                        comp iden k 
                        ∎)
      in proof
         qcomp (abs (qr f)) (abs (qs f))
         ≅⟨ qcompabsabs ⟩
         abs (compSpan (qr f) (qs f))
         ≅⟨ sound _ _ lem ⟩
         abs idSpan
         ∎}


{-

restSpanIdem : ∀{A B}(f : Span A B) → Idem
restSpanIdem {A}{B} f = record {
  E = A; 
  e = abs (restSpan f); 
  law = sound _ _ (~trans (~cong (liftbeta _) (liftbeta _)) R1p)}

restSpanSplit : ∀{A B}(f : Span A B) → Split (restSpanIdem f)
restSpanSplit {A}{B} f = let open Span f
  in record { 
  B    = A'; 
  s    = abs (record {A' = A'; mhom = iden; fhom = mhom; m∈ = iso idiso }); 
  r    = abs (record { A' = A'; mhom = mhom; fhom = iden; m∈ = m∈ });
  law1 = let open Pullback (proj₁ (pul (iden {A'}) (iso idiso)))
             open Square sq
  
             myp : Pullback (iden {A'}) (iden {A'})
             myp = trivialpul (iden {A'})

             lem : h ≅ k
             lem = proof 
                   h 
                   ≅⟨ sym idl ⟩ 
                   comp iden h
                   ≅⟨ scom ⟩
                   comp iden k
                   ≅⟨ idl ⟩
                   k 
                   ∎
         in sound 
         _ 
         _ 
         (~trans (~cong (liftbeta _) (liftbeta _)) 
                 (spaneq (PMap.mor (fst (Pullback.prop myp sq))) 
                         (pullbackiso myp (proj₁ (pul (iden {A'}) (iso idiso))))
                         refl
                         (proof 
                          comp mhom h 
                          ≅⟨ cong (comp mhom) lem ⟩ 
                          comp mhom k 
                          ∎)));
  law2 = let open Pullback (proj₁ (pul mhom m∈)) 
             open Square sq
             myp : Pullback mhom mhom 
             myp = monic→pullback (mon m∈)
         in sound 
         _ 
         _ 
         (~trans (~cong (liftbeta _) (liftbeta _)) 
                 (spaneq (PMap.mor (fst (Pullback.prop myp sq))) 
                        (pullbackiso myp (proj₁ (pul mhom m∈))) 
                        refl 
                        (proof 
                         comp iden h 
                         ≅⟨ idl ⟩
                         h
                         ≅⟨ mon m∈ scom ⟩ 
                         k
                         ≅⟨ sym idl ⟩
                         comp iden k 
                         ∎)))}

-}

-}
-}
