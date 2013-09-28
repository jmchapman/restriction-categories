{-# OPTIONS --type-in-type #-}
open import Categories
open import Stable
module Soundness (X : Cat) (M : StableSys X) where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import RestrictionCat
open import PartialMaps X M
open Cat X
open import Categories.Pullbacks X
open StableSys X M
open import Data.Product
open import Categories.Pullbacks.PullbacksLemmas X
open import Categories.Pullbacks.PastingLemmas X
open import Utilities
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
Span~restp {A}{B}{mf}{m'f'} (spaneq s i q r) = spaneq s i q q

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

RestPartials : RestCat
RestPartials = record {
  cat = Par; 
  rest = λ f → abs (restp (rep f)); 
  R1 = λ {A B mf} → trans 
    (ax1 _ _ (~trans (~cong ~refl (ax3 _)) 
                      (R1p {mf = rep mf}))) 
    (ax2 _); 
  R2 = λ {A B C mf m'f'} → ax1 
    _ 
    _ 
    (~trans (~trans (~cong (ax3 _) (ax3 _))
                    (R2p {mf = rep mf} {m'f' = rep m'f'})) 
            (~sym (~cong (ax3 _) (ax3 _))));
  R3 = λ {A B C mf m'f'} → ax1 
    _ 
    _  
    (~trans (~cong (ax3 _) (ax3 _)) 
            (~trans (R3p {mf = rep mf} {m'f' = rep m'f'}) 
                    (Span~restp (~sym (~trans (ax3 _) 
                                              (~cong ~refl (ax3 _)))))));
  R4 = λ {A B C mf m'f'} → ax1 
    _ 
    _ 
    (~trans (~cong (ax3 _) ~refl) 
            (~trans (R4p {mf = rep mf} {m'f' = rep m'f'}) 
                    (~cong ~refl 
                           (~trans (Span~restp (~sym (ax3 _))) 
                                   (~sym (ax3 _))))))}

-- every restriction in Par splits

open import Categories.Idems Par
open Categories.Isos X

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

