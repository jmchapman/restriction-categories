{-# OPTIONS --type-in-type #-}
open import Categories
open import PartialMaps.Stable
module Soundness (X : Cat) (M : StableSys X) where
open import Function
open import Utilities
open import Restriction.Cat
open import PartialMaps.Cat X M
open Cat X
open import Categories.Pullbacks X
open StableSys X M
open import Data.Product
open import Categories.Pullbacks.PullbacksLemmas X
open import Categories.Pullbacks.PastingLemmas X

import Categories.Isos

restp : ∀{A B} → Span A B → Span A A
restp mf = record { 
  A' = A'; 
  mhom = mhom; 
  fhom = mhom; 
  m∈ = m∈ }
  where open Span mf

Span~restp : ∀{A B}{mf m'f' : Span A B} → mf ~Span~ m'f' → 
             restp mf ~Span~ restp m'f'
Span~restp (spaneq s i q r) = spaneq s i q q

.R1p : ∀{A B} → {mf : Span A B} → compspan mf (restp mf) ~Span~ mf
R1p {A}{B}{mf} =
  let open Span mf

      p : Pullback mhom mhom
      p = proj₁ (pul mhom m∈)

      open Pullback p 
      open Square sq

      p' : Pullback mhom mhom
      p' = monic→pullback (mon m∈)

  in spaneq h 
            (pullbackiso p' p) 
            (proof 
             comp mhom h 
             ≅⟨ refl ⟩ 
             comp mhom h 
             ∎) 
            (proof
             comp fhom h 
             ≅⟨ cong (comp fhom) (mon m∈ scom) ⟩ 
             comp fhom k 
             ∎)

.R2p : ∀{A B C}{mf : Span A B}{m'f' : Span A C} → 
       compspan (restp mf) (restp m'f') ~Span~ compspan (restp m'f') (restp mf)
R2p {mf = mf} {m'f' = m'f'} = 
  let open Span mf renaming (mhom to m; fhom to f)
      open Span m'f' renaming (A' to A''; mhom to m'; fhom to f'; m∈ to m'∈) 

      p : Pullback m m'
      p = sympul (proj₁ (pul m' m∈))

      open Pullback p
      open Square sq

      p' : Pullback m m'
      p' = proj₁ (pul m m'∈)

      open Pullback p' renaming (sq to sq'; prop to prop')
      open Square sq' renaming (W to W'; h to h'; k to k'; scom to scom')

      pu : PMap sq sq'
      pu = fst (prop' sq)

      open PMap pu renaming (mor to u)
  in spaneq u 
            (pullbackiso p' p) 
            (proof
             comp (comp m h') u 
             ≅⟨ ass ⟩
             comp m (comp h' u) 
             ≅⟨ cong (comp m) prop1 ⟩
             comp m h 
             ≅⟨ scom ⟩ 
             comp m' k ∎) 
            (proof
             comp (comp m' k') u 
             ≅⟨ ass ⟩
             comp m' (comp k' u) 
             ≅⟨ cong (comp m') prop2 ⟩
             comp m' k 
             ≅⟨ sym scom ⟩ 
             comp m h 
             ∎)
 
.R3p : ∀{A B C}{mf : Span A B}{m'f' : Span A C} →
       compspan (restp m'f') (restp mf) ~Span~ restp (compspan m'f' (restp mf))
R3p {mf = mf} {m'f' = m'f'} = 
  let open Span mf renaming (mhom to m; fhom to f)
      open Span m'f' renaming (A' to A''; mhom to m'; fhom to f'; m∈ to m'∈) 

      p : Pullback m m'
      p = proj₁ (pul m m'∈)

      open Pullback p
      open Square sq
      open Categories.Isos X

  in spaneq
    iden 
    idiso 
    (proof
     comp (comp m h) iden
     ≅⟨ idr ⟩
     comp m h
     ∎)
    (proof 
     comp (comp m h) iden 
     ≅⟨ idr ⟩ 
     comp m h 
     ≅⟨ scom ⟩ 
     comp m' k 
     ∎)

.R4p : ∀{A B C}{mf : Span A B}{m'f' : Span B C} →
       compspan (restp m'f') mf ~Span~ compspan mf (restp (compspan m'f' mf))
R4p {mf = mf} {m'f' = m'f'} = 
  let open Span mf renaming (mhom to m; fhom to f)
      open Span m'f' renaming (A' to A''; mhom to m'; fhom to f'; m∈ to m'∈)

      p : Pullback f m'
      p = proj₁ (pul f m'∈)

      open Pullback p 
      open Square sq

      p'' : Pullback (comp m h) m
      p'' = lem1 (monic→pullback (mon m∈)) (trivialpul h)

      open Pullback p'' renaming (sq to sq''; prop to prop'')

      p' : Pullback (comp m h) m
      p' = proj₁ (pul (comp m h) m∈)

      open Pullback p' renaming (sq to sq'; prop to prop')
      open Square sq' renaming (W to W'; h to h'; k to k'; scom to scom')

      pu : PMap sq'' sq'
      pu = fst (prop' sq'')

      open PMap pu renaming (mor to u)

  in spaneq 
    u 
    (pullbackiso p' p'') 
    (proof 
     comp (comp (comp m h) h') u 
     ≅⟨ ass ⟩ 
     comp (comp m h) (comp h' u) 
     ≅⟨ cong (comp (comp m h)) prop1  ⟩ 
     comp (comp m h) iden 
     ≅⟨ idr ⟩ 
     comp m h 
     ∎) 
    (proof
     comp (comp f k') u
     ≅⟨ ass ⟩
     comp f (comp k' u)
     ≅⟨ cong (comp f) prop2 ⟩
     comp f (comp iden h)
     ≅⟨ cong (comp f) idl ⟩
     comp f h
     ≅⟨ scom ⟩
     comp m' k
     ∎)

qrest : ∀{A B} → QSpan A B → QSpan A A
qrest = lift (abs ∘ restp) (ax1 _ _ ∘ Span~restp)

.qrestabs≅ : ∀{A B}{mf : Span A B} → qrest (abs mf) ≅ abs (restp mf)
qrestabs≅ {A}{B}{mf} = ax3 (abs ∘ restp) (ax1 _ _ ∘ Span~restp) mf

.qR1 : ∀{A B}{f : QSpan A B} → qcomp f (qrest f) ≅ f
qR1 {A}{B}{f} = Quotient.lift (quot (Span A B) Span~EqR) 
                              {λ y → qcomp y (qrest y) ≅ y}
                              (λ a → 
                                proof 
                                qcomp (abs a) (qrest (abs a))
                                ≅⟨ cong (qcomp (abs a)) qrestabs≅ ⟩
                                qcomp (abs a) (abs (restp a))
                                ≅⟨ qcompabsabs ⟩ 
                                abs (compspan a (restp a))
                                ≅⟨ ax1 _ _  R1p ⟩ 
                                abs a 
                                ∎) 
                              (λ x → fixtypes'' 
                                              (ax1 _ _ x)) 
                              f

.qR2 : ∀{A B C}{f : QSpan A B}{g : QSpan A C} → qcomp (qrest g) (qrest f) ≅ qcomp (qrest f) (qrest g)
qR2 {A}{B}{C}{f}{g} = Quotient.lift (quot (Span A C) Span~EqR)
                                    {λ y → qcomp (qrest y) (qrest f) ≅ qcomp (qrest f) (qrest y)} 
                                    (λ a → Quotient.lift (quot (Span A B) Span~EqR)
                                                         {λ y → qcomp (qrest (abs a)) (qrest y) ≅ qcomp (qrest y) (qrest (abs a))}
                                                         (λ b → 
                                                           proof
                                                           qcomp (qrest (abs a)) (qrest (abs b))
                                                           ≅⟨ cong (λ y → qcomp y (qrest (abs b))) qrestabs≅ ⟩
                                                           qcomp (abs (restp a)) (qrest (abs b))
                                                           ≅⟨ cong (qcomp (abs (restp a))) qrestabs≅ ⟩
                                                           qcomp (abs (restp a)) (abs (restp b))
                                                           ≅⟨ qcompabsabs ⟩
                                                           abs (compspan (restp a) (restp b))
                                                           ≅⟨ ax1 _ _ (R2p {mf = a}{m'f' = b}) ⟩
                                                           abs (compspan (restp b) (restp a))
                                                           ≅⟨ sym qcompabsabs ⟩
                                                           qcomp (abs (restp b)) (abs (restp a))
                                                           ≅⟨ cong (qcomp (abs (restp b))) (sym qrestabs≅) ⟩
                                                           qcomp (abs (restp b)) (qrest (abs a))
                                                           ≅⟨ cong (λ y → qcomp y (qrest (abs a))) (sym qrestabs≅) ⟩
                                                           qcomp (qrest (abs b)) (qrest (abs a))
                                                           ∎) 
                                                         (λ x → fixtypes' (cong (qcomp (qrest (abs a)) ∘ qrest) (ax1 _ _ x)))
                                                                         
                                                         f) 
                                    (λ x → fixtypes' (cong (λ y → qcomp (qrest y) (qrest f)) (ax1 _ _ x)))
                           
                                    g

.qR3 : ∀{A B C}{f : QSpan A B}{g : QSpan A C} → qcomp (qrest g) (qrest f) ≅ qrest (qcomp g (qrest f))
qR3 {A}{B}{C}{f}{g} = Quotient.lift (quot (Span A C) Span~EqR)
                                    {λ y → qcomp (qrest y) (qrest f) ≅ qrest (qcomp y (qrest f))} 
                                    (λ a → Quotient.lift (quot (Span A B) Span~EqR)
                                                         {λ y → qcomp (qrest (abs a)) (qrest y) ≅ qrest (qcomp (abs a) (qrest y))}
                                                         (λ b → 
                                                           proof
                                                           qcomp (qrest (abs a)) (qrest (abs b))
                                                           ≅⟨ cong (λ y → qcomp y (qrest (abs b))) qrestabs≅ ⟩
                                                           qcomp (abs (restp a)) (qrest (abs b))
                                                           ≅⟨ cong (qcomp (abs (restp a))) qrestabs≅ ⟩
                                                           qcomp (abs (restp a)) (abs (restp b))
                                                           ≅⟨ qcompabsabs ⟩
                                                           abs (compspan (restp a) (restp b))
                                                           ≅⟨ ax1 _ _ (R3p {mf = b}{m'f' = a}) ⟩
                                                           abs (restp (compspan a (restp b)))
                                                           ≅⟨ sym qrestabs≅ ⟩
                                                           qrest (abs (compspan a (restp b)))
                                                           ≅⟨ cong qrest (sym qcompabsabs) ⟩
                                                           qrest (qcomp (abs a) (abs (restp b)))
                                                           ≅⟨ cong (qrest ∘ qcomp (abs a)) (sym qrestabs≅) ⟩
                                                           qrest (qcomp (abs a) (qrest (abs b)))
                                                           ∎) 
                                                         (λ x → fixtypes' (cong (qcomp (qrest (abs a)) ∘ qrest) (ax1 _ _ x)))
                                             
                                                         f) 
                                    (λ x → fixtypes' (cong (λ y → qcomp (qrest y) (qrest f)) (ax1 _ _ x)))
                          
                                    g

.qR4 : ∀{A B C}{f : QSpan A B}{g : QSpan B C} → qcomp (qrest g) f ≅ qcomp f (qrest (qcomp g f))
qR4 {A}{B}{C}{f}{g} = Quotient.lift (quot (Span B C) Span~EqR)
                                    {λ y → qcomp (qrest y) f ≅ qcomp f (qrest (qcomp y f))}
                                    (λ a → Quotient.lift (quot (Span A B) Span~EqR)
                                                         {λ y → qcomp (qrest (abs a)) y ≅ qcomp y (qrest (qcomp (abs a) y))}
                                                         (λ b → 
                                                           proof
                                                           qcomp (qrest (abs a)) (abs b)
                                                           ≅⟨ cong (λ y → qcomp y (abs b)) qrestabs≅ ⟩
                                                           qcomp (abs (restp a)) (abs b)
                                                           ≅⟨ qcompabsabs ⟩
                                                           abs (compspan (restp a) b)
                                                           ≅⟨ ax1 _ _ (R4p {mf = b}{m'f' = a}) ⟩
                                                           abs (compspan b (restp (compspan a b)))
                                                           ≅⟨ sym qcompabsabs ⟩
                                                           qcomp (abs b) (abs (restp (compspan a b)))
                                                           ≅⟨ cong (qcomp (abs b)) (sym qrestabs≅) ⟩
                                                           qcomp (abs b) (qrest (abs (compspan a b)))
                                                           ≅⟨ cong (qcomp (abs b) ∘ qrest) (sym qcompabsabs) ⟩
                                                           qcomp (abs b) (qrest (qcomp (abs a) (abs b)))
                                                           ∎) 
                                                         (λ x → fixtypes' (cong (qcomp (qrest (abs a))) (ax1 _ _ x)))
                                     
                                                         f)
                                    (λ x → fixtypes' (cong (λ y → qcomp (qrest y) f) (ax1 _ _ x)))
                  
                                    g

RestPartials : RestCat
RestPartials = record { 
  cat = Par; 
  rest = qrest;
  R1 = qR1;
  R2 = qR2;
  R3 = qR3;
  R4 = qR4}

-- every restriction in Par splits

open import Categories.Idems Par
open Categories.Isos X

restpIdem : ∀{A B}(f : QSpan A B) → Idem
restpIdem {A}{B} f = record {
  E = A; 
  e = qrest f;
  law = Quotient.lift (quot (Span A B) Span~EqR)
                      {λ y → qcomp (qrest y) (qrest y) ≅ qrest y} 
                      (λ a → 
                        proof
                        qcomp (qrest (abs a)) (qrest (abs a))
                        ≅⟨ cong (λ y → qcomp y y) qrestabs≅ ⟩
                        qcomp (abs (restp a)) (abs (restp a))
                        ≅⟨ qcompabsabs ⟩
                        abs (compspan (restp a) (restp a))
                        ≅⟨ ax1 _ _ R1p ⟩
                        abs (restp a)
                        ≅⟨ sym qrestabs≅ ⟩
                        qrest (abs a)
                        ∎) 
                      (λ x → fixtypes' (cong (λ y → qcomp (qrest y) (qrest y)) (ax1 _ _ x)))
                                      
                      f}

qs : ∀{A B}(f : Span A B) → Span (Span.A' f) A
qs f = 
  let open Span f
  in record { A' = A'; mhom = iden; fhom = mhom; m∈ = iso idiso }

qr : ∀{A B}(f : Span A B) → Span A (Span.A' f)
qr f = 
  let open Span f
  in record { A' = A'; mhom = mhom; fhom = iden; m∈ = m∈ }

restpSplit : ∀{A B}(f : Span A B) → Split (restpIdem (abs f))
restpSplit {A}{B} f = 
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

          lem' : compspan (qs f) (qr f) ~Span~ restp f
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
         abs (compspan (qs f) (qr f))
         ≅⟨ ax1 _ _ lem' ⟩
         abs (restp f)
         ≅⟨ sym qrestabs≅ ⟩
         qrest (abs f)
         ∎;
    law2 = 
      let open Pullback (proj₁ (pul mhom m∈)) 
          open Square sq
          
          myp : Pullback mhom mhom 
          myp = monic→pullback (mon m∈)
  
          lem : compspan (qr f) (qs f) ~Span~ idspan
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
         abs (compspan (qr f) (qs f))
         ≅⟨ ax1 _ _ lem ⟩
         abs idspan
         ∎}


{-

restpIdem : ∀{A B}(f : Span A B) → Idem
restpIdem {A}{B} f = record {
  E = A; 
  e = abs (restp f); 
  law = ax1 _ _ (~trans (~cong (ax3 _) (ax3 _)) R1p)}

restpSplit : ∀{A B}(f : Span A B) → Split (restpIdem f)
restpSplit {A}{B} f = let open Span f
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
         in ax1 
         _ 
         _ 
         (~trans (~cong (ax3 _) (ax3 _)) 
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
         in ax1 
         _ 
         _ 
         (~trans (~cong (ax3 _) (ax3 _)) 
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
