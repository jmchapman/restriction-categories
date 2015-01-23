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

BRestIdemSplit : (i : Idem SC) → Σ (Idem cat) (isRestIdem X)
BRestIdemSplit (idem p m _) = restIdemMorIsRestIdem X {p}{p} m

sRestIdemSplit : (i : Idem SC) → isRestIdem RSC i → Cat.Hom SC (BRestIdemSplit i) (Idem.E i) --IdemMor _ (proj₁ (BRestIdemSplit i)) (proj₁ (Idem.E i))
sRestIdemSplit (idem (idem _ e idemLaw , q) m _) r =
  let idemmor f _ = m
  in idemmor (hat m)
             (proof
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
              ∎)

rRestIdemSplit : (i : Idem SC) → isRestIdem RSC i → Cat.Hom SC (Idem.E i) (BRestIdemSplit i)
rRestIdemSplit (idem (idem _ e idemLaw , q) m _) r =
  let idemmor f _ = m
  in idemmor (hat m)
             (proof
              comp (hat m) (comp (hat m) e) 
              ≅⟨ sym ass ⟩
              comp (comp (hat m) (hat m)) e 
              ≅⟨ cong (λ x → comp x e) (restIdemMorIsIdemLaw X m) ⟩
              comp (hat m) e
              ≅⟨ ass ⟩
              comp (rest f) (comp e e)
              ≅⟨ cong (comp (rest f)) idemLaw ⟩
              hat m
              ∎)

sl1RestIdemSplit : (i : Idem SC) → isRestIdem RSC i → 
                   comp (hat (Idem.e i)) (hat (Idem.e i)) ≅ IdemMor.imap (Idem.e i) 
sl1RestIdemSplit (idem _ m _) r =
  let idemmor f _ = m
  in proof
     comp (hat m) (hat m)
     ≅⟨ restIdemMorIsIdemLaw X m ⟩
     hat m
     ≅⟨ sym (idemMorEqProj _ r) ⟩
     f
     ∎

restIdemSplit : (i : Idem SC) → isRestIdem RSC i → Split SC i
restIdemSplit i r = 
  let idem _ m _ = i
  in record {
    B = BRestIdemSplit i ;
    s = sRestIdemSplit i r ;
    r = rRestIdemSplit i r ;
    splitLaw1 = idemMorEq _ (sl1RestIdemSplit i r) ;
    splitLaw2 = idemMorEq _ (restIdemMorIsIdemLaw X m) }

SplitRestSplitCat : SplitRestCat
SplitRestSplitCat = record { rcat = RSC ; restIdemSplit = restIdemSplit }

InclRestSplitCat : RestFun X RSC
InclRestSplitCat = record { 
  fun = InclSplitCat cat (restIdemClass X) ; 
  frest = idemMorEq cat idr }
