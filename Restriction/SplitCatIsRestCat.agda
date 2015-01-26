{-# OPTIONS --type-in-type #-}
open import Restriction.Cat

module Restriction.SplitCatIsRestCat (X : RestCat) where

open import Utilities
open RestCat X
open import Categories 
open Cat cat
open import Categories.Idems cat
open import Categories.Splits cat

hat : {i i' : Idem} → IdemMor i i' → Hom (Idem.E i) (Idem.E i)
hat {idem _ e _} (idemmor f _) = comp (rest f) e 

hatImapLaw : {i i' : Idem}(m : IdemMor i i') → 
             comp (Idem.e i) (comp (hat m) (Idem.e i)) ≅ hat m 
hatImapLaw {i} (idemmor f q) = 
  let open Idem i
  in
    proof
    comp e (comp (comp (rest f) e) e)
    ≅⟨ cong (comp e) ass ⟩
    comp e (comp (rest f) (comp e e))
    ≅⟨ cong (comp e ∘ comp (rest f)) idemLaw ⟩
    comp e (comp (rest f) e)
    ≅⟨ cong (comp e) R4 ⟩
    comp e (comp e (rest (comp f e)))
    ≅⟨ sym ass ⟩
    comp (comp e e) (rest (comp f e))
    ≅⟨ cong (λ y → comp y (rest (comp f e))) idemLaw ⟩
    comp e (rest (comp f e))
    ≅⟨ sym R4 ⟩
    comp (rest f) e
    ∎

restIdemMor : {i i' : Idem} → IdemMor i i' → IdemMor i i
restIdemMor {i} m = idemmor (hat m) (hatImapLaw m)

restIdemMorComm : {i i' : Idem}(m : IdemMor i i') →
                  hat m ≅ comp (Idem.e i) (rest (IdemMor.imap m))
restIdemMorComm {idem _ e _} m =
  let idemmor f p = m
  in
    proof
    comp (rest f) e
    ≅⟨ R4 ⟩
    comp e (rest (comp f e))
    ≅⟨ cong (comp e ∘ rest) (idemMorPrecomp m) ⟩
    comp e (rest f)
    ∎           

R1split : {E : IdemClass}{p q : Σ Idem (IdemClass.∈class E)}
          {f : IdemMor (proj₁ p) (proj₁ q)} → compIdemMor f (restIdemMor f) ≅ f
R1split {p = i , _}{_}{f = f} = 
  let open Idem i
      open IdemMor f
  in 
    idemMorEq 
      (proof
       comp imap (comp (rest imap) e)       
       ≅⟨ sym ass ⟩
       comp (comp imap (rest imap)) e 
       ≅⟨ cong (λ y → comp y e) R1 ⟩
       comp imap e 
       ≅⟨ idemMorPrecomp f ⟩ 
       imap 
       ∎)

R2split : {E : IdemClass}{p q r : Σ Idem (IdemClass.∈class E)} 
           {f : IdemMor (proj₁ p) (proj₁ q)}{g : IdemMor (proj₁ p) (proj₁ r)} →
           compIdemMor (restIdemMor f) (restIdemMor g) ≅
           compIdemMor (restIdemMor g) (restIdemMor f)
R2split {p = i , _}{f = f}{g} =
  let open Idem i
      open IdemMor f
      open IdemMor g renaming (imap to imap')
  in 
    idemMorEq 
      (proof
       comp (comp (rest imap) e) (comp (rest imap') e) 
       ≅⟨ cong (λ y → comp y (comp (rest imap') e)) (restIdemMorComm f) ⟩
       comp (comp e (rest imap)) (comp (rest imap') e) 
       ≅⟨ ass ⟩
       comp e (comp (rest imap) (comp (rest imap') e)) 
       ≅⟨ cong (comp e) (sym ass) ⟩
       comp e (comp (comp (rest imap) (rest imap')) e) 
       ≅⟨ cong (λ y → comp e (comp y e)) R2 ⟩
       comp e (comp (comp (rest imap') (rest imap)) e) 
       ≅⟨ cong (comp e) ass ⟩
       comp e (comp (rest imap') (comp (rest imap) e)) 
       ≅⟨ sym ass ⟩
       comp (comp e (rest imap')) (comp (rest imap) e) 
       ≅⟨ cong (λ y → comp y (comp (rest imap) e)) (sym (restIdemMorComm g)) ⟩
       comp (comp (rest imap') e) (comp (rest imap) e) 
       ∎)

R3split : {E : IdemClass}{p q r : Σ Idem (IdemClass.∈class E)} 
           {f : IdemMor (proj₁ p) (proj₁ q)}{g : IdemMor (proj₁ p) (proj₁ r)} →
           compIdemMor (restIdemMor g) (restIdemMor f) ≅
           restIdemMor (compIdemMor g (restIdemMor f))
R3split {p = i , _}{f = f}{g} =
  let open Idem i
      open IdemMor f
      open IdemMor g renaming (imap to imap')
  in 
    idemMorEq
      (proof
       comp (comp (rest imap') e) (comp (rest imap) e)
       ≅⟨ ass ⟩
       comp (rest imap') (comp e (comp (rest imap) e))
       ≅⟨ cong (comp (rest imap')) (sym ass) ⟩
       comp (rest imap') (comp (comp e (rest imap)) e)
       ≅⟨ cong (λ y → comp (rest imap') (comp y e)) (sym (restIdemMorComm f)) ⟩
       comp (rest imap') (comp (comp (rest imap) e) e)
       ≅⟨ cong (comp (rest imap')) ass ⟩
       comp (rest imap') (comp (rest imap) (comp  e e))
       ≅⟨ cong (comp (rest imap') ∘ comp (rest imap)) idemLaw ⟩
       comp (rest imap') (comp (rest imap) e)
       ≅⟨ sym ass ⟩
       comp (comp (rest imap') (rest imap)) e
       ≅⟨ cong (λ y → comp y e) R3 ⟩
       comp (rest (comp imap' (rest imap))) e
       ≅⟨ cong (λ y → comp (rest (comp y (rest imap))) e) (sym (idemMorPrecomp g)) ⟩
       comp (rest (comp (comp imap' e) (rest imap))) e
       ≅⟨ cong (λ y → comp (rest y) e) ass ⟩
       comp (rest (comp imap' (comp e (rest imap)))) e
       ≅⟨ cong (λ y → comp (rest (comp imap' y)) e) (sym (restIdemMorComm f)) ⟩
       comp (rest (comp imap' (comp (rest imap) e))) e
       ∎)
 
R4split : {E : IdemClass}{p q r : Σ Idem (IdemClass.∈class E)} 
           {f : IdemMor (proj₁ p) (proj₁ q)}{g : IdemMor (proj₁ q) (proj₁ r)} →
           compIdemMor (restIdemMor g) f ≅
           compIdemMor f (restIdemMor (compIdemMor g f))
R4split {p = i , _}{i' , _}{f = f}{g} =
  let open Idem i
      open Idem i' renaming (e to e')
      open IdemMor f
      open IdemMor g renaming (imap to imap')
  in 
    idemMorEq
      (proof 
       comp (comp (rest imap') e') imap 
       ≅⟨ ass ⟩ 
       comp (rest imap') (comp e' imap)
       ≅⟨ cong (comp (rest imap')) (idemMorPostcomp f) ⟩ 
       comp (rest imap') imap
       ≅⟨ cong (comp (rest imap')) (sym (idemMorPrecomp f)) ⟩
       comp (rest imap') (comp imap e)
       ≅⟨ sym ass ⟩
       comp (comp (rest imap') imap) e
       ≅⟨ cong (λ y → comp y e) R4 ⟩
       comp (comp imap (rest (comp imap' imap))) e
       ≅⟨ ass ⟩
       comp imap (comp (rest (comp imap' imap)) e) 
       ∎)

RestSplitCat : (E : IdemClass) → RestCat
RestSplitCat E = 
  let open IdemClass E 
  in record { 
    cat = SplitCat E ; 
    rest = restIdemMor ; 
    R1 = λ {p}{q}{f} → R1split {E}{p}{q}{f}; 
    R2 = λ {p}{q}{r}{f}{g} → R2split {E}{p}{q}{r}{f}{g};
    R3 = λ {p}{q}{r}{f}{g} → R3split {E}{p}{q}{r}{f}{g} ; 
    R4 = λ {p}{q}{r}{f}{g} → R4split {E}{p}{q}{r}{f}{g} }
