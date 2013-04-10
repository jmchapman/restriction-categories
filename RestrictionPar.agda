{-# OPTIONS --type-in-type #-}
open import Categories
open import Stable
module RestrictionPar (X : Cat) (M : StableSys X) where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import RestrictionCat
open PartialCats X M
open Cat X
open import Pullbacks X
open StableSys X M
open import Data.Product
open import PullbacksLemmas X

restp : ∀{A B} → Span A B → Span A A
restp mf = record { 
  A' = A'; 
  mhom = mhom; 
  fhom = mhom; 
  m∈ = m∈ }
  where open Span mf

R1p : ∀{A B} → {mf : Span A B} → compspan mf (restp mf) ≅ mf
R1p {mf = mf} = 
  let open Span mf
  
      p : Pullback mhom mhom
      p = proj₁ (pul mhom m∈)

      open Pullback p 
      open Square sq

      p' : Pullback mhom mhom
      p' = monic→pullback (mon m∈)
      
  in quotient 
    _
    _ 
    h 
    (pullbackiso p' p) 
    (proof 
     comp mhom h 
     ≅⟨ refl ⟩ 
     comp mhom h ∎) 
    (proof 
     comp fhom h 
     ≅⟨ cong (comp fhom) (mon m∈ scom) ⟩ 
     comp fhom k ∎)
  
R2p : ∀{A B C}{mf : Span A B}{m'f' : Span A C} → 
      compspan (restp mf) (restp m'f') ≅ compspan (restp m'f') (restp mf)
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
      pu = proj₁ (prop' sq)

      open PMap pu renaming (mor to u)
  in quotient 
    _ 
    _ 
    u 
    (pullbackiso p' p) 
    (proof 
     comp (comp m h') u 
     ≅⟨ ass ⟩ 
     comp m (comp h' u) 
     ≅⟨ cong (comp m) prop1 ⟩ 
     comp m h 
     ≅⟨ scom ⟩ 
     comp m' k 
     ∎) 
    (proof 
     comp (comp m' k') u 
     ≅⟨ ass ⟩ 
     comp m' (comp k' u) 
     ≅⟨ cong (comp m') prop2 ⟩ 
     comp m' k 
     ≅⟨ sym scom ⟩ 
     comp m h
     ∎)

R3p : ∀{A B C}{mf : Span A B}{m'f' : Span A C} →
      compspan (restp m'f') (restp mf) ≅ restp (compspan m'f' (restp mf))
R3p {mf = mf} {m'f' = m'f'} = 
  let open Span mf renaming (mhom to m; fhom to f)
      open Span m'f' renaming (A' to A''; mhom to m'; fhom to f'; m∈ to m'∈) 

      p : Pullback m m'
      p = proj₁ (pul m m'∈)

      open Pullback p
      open Square sq
      open Isos X

  in quotient 
    _ 
    _ 
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

R4p : ∀{A B C}{mf : Span A B}{m'f' : Span B C} →
      compspan (restp m'f') mf ≅ compspan mf (restp (compspan m'f' mf))
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
      pu = proj₁ (prop' sq'')

      open PMap pu renaming (mor to u)

  in quotient 
    _ 
    _ 
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
  rest = restp; 
  R1 = R1p; 
  R2 = λ {A B C mf m'f'} → R2p {A}{B}{C}{mf}{m'f'}; 
  R3 = λ {A B C mf m'f'} → R3p {A}{B}{C}{mf}{m'f'}; 
  R4 = λ {A B C mf m'f'} → R4p {A}{B}{C}{mf}{m'f'} }

-- every restriction in Par splits
open Idems Par
open Isos X

restpIdem : ∀{A B}(f : Span A B) → Idem
restpIdem {A}{B} f = record {E = A; e = restp f; law = R1p}

--pullbackiso : ∀{X Y Z}{f : Hom X Z}{g : Hom Y Z}(p p' : Pullback f g) → 
--                Iso (mor (proj₁ (prop p (sq p'))))
  

restpSplit : ∀{A B}(f : Span A B) → Split (restpIdem f)
restpSplit {A}{B} f = let open Span f
  in record { 
  B    = A'; 
  s    = record {A' = A'; mhom = iden; fhom = mhom; m∈ = iso idiso }; 
  r    = record {A' = A'; mhom = mhom; fhom = iden; m∈ = m∈ }; 
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
         in quotient 
           _ 
           _ 
           (PMap.mor (proj₁ (Pullback.prop myp sq)))
           (pullbackiso myp (proj₁ (pul (iden {A'}) (iso idiso))))
           refl
           (proof 
            comp mhom h 
            ≅⟨ cong (comp mhom) lem ⟩ 
            comp mhom k 
            ∎);
  law2 = {!!} }