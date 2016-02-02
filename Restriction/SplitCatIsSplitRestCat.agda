{-# OPTIONS --type-in-type #-}
open import Restriction.Cat

module Restriction.SplitCatIsSplitRestCat (X : RestCat) where

open import Utilities
open import Categories
open RestCat X
open Cat cat
open import Categories.Idems 
open import Categories.Splits
import Restriction.Idems
open import Restriction.SplitCatIsRestCat X
open import Restriction.SplitRestCats
open import Restriction.Functors

SC = SplitCat cat (Restriction.Idems.restIdemClass X)
RSC = RestSplitCat (Restriction.Idems.restIdemClass X)
ObjSC = Cat.Obj SC
HomSC = Cat.Hom SC
IdemSC = Idem SC
SplitSC = Split SC
isRestIdemRSC = Restriction.Idems.isRestIdem RSC

open Restriction.Idems X

BRestIdemSplit : (i : IdemSC) → ObjSC
BRestIdemSplit (idem p m _) = restIdemMorIsRestIdem {p}{p} m

sRestIdemSplit : (i : IdemSC) → isRestIdemRSC i → HomSC (BRestIdemSplit i) (Idem.E i)
sRestIdemSplit (idem (idem _ e idemLaw , q) m _) r =
  let idemmor f _ = m
  in idemmor (hat m)
             (proof
              comp e (comp (hat m) (hat m))
              ≅⟨ cong (comp e) (restIdemMorIsIdemLaw m) ⟩
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

rRestIdemSplit : (i : IdemSC) → isRestIdemRSC i → HomSC (Idem.E i) (BRestIdemSplit i)
rRestIdemSplit (idem (idem _ e idemLaw , q) m _) r =
  let idemmor f _ = m
  in idemmor (hat m)
             (proof
              comp (hat m) (comp (hat m) e) 
              ≅⟨ sym ass ⟩
              comp (comp (hat m) (hat m)) e 
              ≅⟨ cong (λ x → comp x e) (restIdemMorIsIdemLaw m) ⟩
              comp (hat m) e
              ≅⟨ ass ⟩
              comp (rest f) (comp e e)
              ≅⟨ cong (comp (rest f)) idemLaw ⟩
              hat m
              ∎)

sl1RestIdemSplit : (i : Idem SC) → isRestIdemRSC i → 
                   comp (hat (Idem.e i)) (hat (Idem.e i)) ≅ IdemMor.imap (Idem.e i) 
sl1RestIdemSplit (idem E m _) r =
  let idemmor f _ = m
  in proof
     comp (hat m) (hat m)
     ≅⟨ restIdemMorIsIdemLaw m ⟩
     hat m
     ≅⟨ sym (cong {B = λ _ → Hom (Idem.E (proj₁ E)) (Idem.E (proj₁ E))} IdemMor.imap r) ⟩
     f
     ∎

restIdemSplit : (i : IdemSC) → isRestIdemRSC i → SplitSC i
restIdemSplit i r = 
  let idem _ m _ = i
  in record {
    B = BRestIdemSplit i ;
    s = sRestIdemSplit i r ;
    r = rRestIdemSplit i r ;
    splitLaw1 = idemMorEq _ (sl1RestIdemSplit i r) ;
    splitLaw2 = idemMorEq _ (restIdemMorIsIdemLaw m) }

SplitRestSplitCat : SplitRestCat
SplitRestSplitCat = record { rcat = RSC ; restIdemSplit = restIdemSplit }

InclRestSplitCat : RestFun X RSC
InclRestSplitCat = record { 
  fun = InclSplitCat cat restIdemClass ; 
  frest = idemMorEq cat idr }

