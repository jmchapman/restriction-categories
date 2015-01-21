{-# OPTIONS --type-in-type #-}
open import Restriction.Cat

module Restriction.SplitCatIsSplitRestCat (X : RestCat) where

open import Utilities
open import Categories
open RestCat X
open Cat cat
open import Categories.Idems 
open import Categories.Splits
open import Restriction.Idems
open import Restriction.SplitCatIsRestCat X
open import Restriction.SplitRestCats
open import Restriction.Functors

SC = SplitCat cat (restIdemClass X)
RSC = RestSplitCat (restIdemClass X)

restIdemSplit : (i : Idem SC) → isRestIdem RSC i → Split SC i
restIdemSplit i r = 
  let open Idem _ i renaming (E to p; e to m; idemLaw to mlaw)
      j , q = p
      open IdemMor _ m renaming (imap to f)
      open Idem _ j

      sImapLaw : comp e (comp (hat m) (hat m)) ≅ hat m
      sImapLaw = 
        proof
        comp e (comp (hat m) (hat m))
        ≅⟨ cong (comp e) (restIdemMorIsIdemLaw X m) ⟩
        comp e (hat m)
        ≅⟨ cong (comp e) (restIdemMorComm m) ⟩
        comp e (comp e (rest f))
        ≅⟨ sym ass ⟩
        comp (comp e e) (rest f)
        ≅⟨ cong (λ x → comp x (rest f)) idemLaw ⟩
        comp e (rest f)
        ≅⟨ sym (restIdemMorComm m) ⟩
        hat m
        ∎

      rImapLaw : comp (hat m) (comp (hat m) e) ≅ hat m
      rImapLaw = 
        proof
        comp (hat m) (comp (hat m) e) 
        ≅⟨ sym ass ⟩
        comp (comp (hat m) (hat m)) e 
        ≅⟨ cong (λ x → comp x e) (restIdemMorIsIdemLaw X m) ⟩
        comp (hat m) e
        ≅⟨ ass ⟩
        comp (rest f) (comp e e)
        ≅⟨ cong (comp (rest f)) idemLaw ⟩
        hat m
        ∎

      splitLaw1 : comp (hat m) (hat m) ≅ f
      splitLaw1 = 
        proof
        comp (hat m) (hat m)
        ≅⟨ restIdemMorIsIdemLaw X m ⟩
        hat m
        ≅⟨ sym (idemMorEqProj _ r) ⟩
        f
        ∎

  in record {
    B = restIdemMorIsRestIdem X {p}{p} m ;
    s = idemmor (hat m) sImapLaw ;
    r = idemmor (hat m) rImapLaw ;
    splitLaw1 = idemMorEq _ splitLaw1 ; 
    splitLaw2 = idemMorEq _ (restIdemMorIsIdemLaw X m) }

SplitRestSplitCat : SplitRestCat
SplitRestSplitCat = record { rcat = RSC ; restIdemSplit = restIdemSplit }

InclRestSplitCat : RestFun X  RSC
InclRestSplitCat = record { 
  fun = InclSplitCat cat (restIdemClass X) ; 
  frest = idemMorEq cat idr }
