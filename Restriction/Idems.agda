{-# OPTIONS --type-in-type #-}
open import Restriction.Cat

module Restriction.Idems (X : RestCat) where

open import Utilities
open import Categories
open RestCat X
open Cat cat
open import Categories.Idems cat
open import Categories.Splits cat
open import Categories.Monos cat
open Lemmata X
open import Restriction.SplitCatIsRestCat X

isRestIdem : Idem → Set
isRestIdem (idem _ e _) = e ≅ rest e

restIdemClass : IdemClass
restIdemClass = record { 
  ∈class = isRestIdem ; 
  id∈class = sym (lemiii idMono) }

-- .restIdemMorIsIdemLaw' : {i i' : Idem}(f : IdemMor i i') → comp (hat f) (hat f) ≅ hat f
-- restIdemMorIsIdemLaw' {i}{i'} f = idemMorEqProj {i} {i} {compIdemMor (restIdemMor f) (restIdemMor f)}
--                                     {restIdemMor f} (Lemmata.lemii (RestSplitCat restIdemClass))

restIdemMorIsIdemLaw : {i i' : Idem}(f : IdemMor i i') → comp (hat f) (hat f) ≅ hat f
restIdemMorIsIdemLaw {i} f = 
  let open Idem i
      open IdemMor f
  in  
    proof
    comp (comp (rest imap) e) (comp (rest imap) e)
    ≅⟨ cong (λ y → comp y (comp (rest imap) e)) (restIdemMorComm f) ⟩
    comp (comp e (rest imap)) (comp (rest imap) e)
    ≅⟨ ass ⟩
    comp e (comp (rest imap) (comp (rest imap) e))
    ≅⟨ cong (comp e) (sym ass) ⟩
    comp e (comp (comp (rest imap) (rest imap)) e)
    ≅⟨ cong (λ y → comp e (comp y e)) lemii ⟩
    comp e (comp (rest imap) e)
    ≅⟨ cong (comp e) (restIdemMorComm f) ⟩
    comp e (comp e (rest imap))
    ≅⟨ sym ass ⟩
    comp (comp e e) (rest imap)
    ≅⟨ cong (λ y → comp y (rest imap)) idemLaw ⟩
    comp e (rest imap)
    ≅⟨ sym (restIdemMorComm f) ⟩
    comp (rest imap) e
    ∎

restIdemMorIsIdem : {i i' : Σ Idem isRestIdem} → IdemMor (proj₁ i) (proj₁ i') → Idem
restIdemMorIsIdem f = idem  _ (hat f) (restIdemMorIsIdemLaw f)

restIdemMorIsRestIdem : {i i' : Σ Idem isRestIdem} → IdemMor (proj₁ i) (proj₁ i') → 
                        Σ Idem isRestIdem
restIdemMorIsRestIdem {i , p}{q} f =
  let open Idem i
      open IdemMor f
  in 
    restIdemMorIsIdem {i , p}{q} f , 
    (proof 
     comp (rest imap) e 
     ≅⟨ cong (comp (rest imap)) p ⟩ 
     comp (rest imap) (rest e) 
     ≅⟨ R3 ⟩ 
     rest (comp imap (rest e))
     ≅⟨ cong (rest ∘ comp imap) (sym p) ⟩ 
     rest (comp imap e)
     ≅⟨ lemiv ⟩ 
     rest (comp (rest imap) e) 
     ∎)

