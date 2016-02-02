{-# OPTIONS --type-in-type #-}
open import Restriction.SplitRestCats

module PartialMaps.MonicClasses (X : SplitRestCat) where

open import Utilities
open import Categories
open import Restriction.Cat
open SplitRestCat X
open RestCat rcat
open Cat cat
open Lemmata rcat
open import Categories.Idems cat
open import Categories.Splits cat
open import Restriction.Totals rcat
open Tot
open import Restriction.Idems rcat
open import Categories.Monos
open import Categories.Isos Total
open import Categories.Pullbacks Total
open import PartialMaps.Stable

record SectionOfRestIdem {B E} (s : Tot B E) : Set where
  constructor sridem
  field e         : Hom E E
        restIdem  : e ≅ rest e
        r         : Hom E B
        splitLaw1 : comp (hom s) r ≅ e
        splitLaw2 : comp r (hom s) ≅ iden {B}

sectionOfRestIdemIdem : ∀{B E}{s : Tot B E} → SectionOfRestIdem s → Idem
sectionOfRestIdemIdem (sridem e p _ _ _) = 
  idem _ 
       e 
       (proof
        comp e e
        ≅⟨ cong (λ x → comp x x) p ⟩
        comp (rest e) (rest e)
        ≅⟨ lemii ⟩
        rest e
        ≅⟨ sym p ⟩
        e
        ∎)

sectionOfRestIdemSplit : ∀{B E}{s : Tot B E}(p : SectionOfRestIdem s) → Split (sectionOfRestIdemIdem p)
sectionOfRestIdemSplit {B}{s = tot s _} (sridem e p r l1 l2) = split B s r l1 l2

sectionOfRestIdemSplit2 : ∀{B E}{s : Tot B E}(p : SectionOfRestIdem s) → Split (sectionOfRestIdemIdem p)
sectionOfRestIdemSplit2 p = restIdemSplit (sectionOfRestIdemIdem p) (SectionOfRestIdem.restIdem p)

mono∈sysSectionsOfRestIdem : ∀{B E}{s : Tot B E} → SectionOfRestIdem s → Mono Total s
mono∈sysSectionsOfRestIdem p {_}{f}{g} q = 
  totEq (sectionIsMono (sectionOfRestIdemSplit p) (cong hom q))

iso∈sysSectionOfRestIdem : ∀{B E}{s : Tot B E} → Iso s → SectionOfRestIdem s
iso∈sysSectionOfRestIdem (iso (tot g _) rinv linv) = 
  sridem iden (sym (lemiii (idMono cat))) g (cong hom rinv) (cong hom linv)

restRetractionProp : ∀{B E}{s : Tot B E}(p : SectionOfRestIdem s) → 
                     SectionOfRestIdem.e p ≅ rest (SectionOfRestIdem.r p)
restRetractionProp {s = s} p  =
  let open SectionOfRestIdem p
  in
    proof
    e
    ≅⟨ restIdem ⟩
    rest e
    ≅⟨ cong rest (sym splitLaw1) ⟩
    rest (comp (hom s) r)
    ≅⟨ lemiv ⟩
    rest (comp (rest (hom s)) r)
    ≅⟨ cong (λ x → rest (comp x r)) (totProp s) ⟩
    rest (comp iden r)
    ≅⟨ cong rest idl ⟩
    rest r
    ∎
  
comp∈sysSectionOfRestIdem : ∀{B E E'}{s : Tot B E}{s' : Tot E E'} → SectionOfRestIdem s → 
                            SectionOfRestIdem s' → SectionOfRestIdem (compTot s' s)
comp∈sysSectionOfRestIdem {s = tot s _}{tot s' _} sr sr' =
  let sridem e p r l1 l2 = sr
      sridem e' p' r' l1' l2' = sr'
  in sridem (rest (comp (comp r r') (rest r'))) 
            (sym lemi) 
            (comp r r') 
            (proof
             comp (comp s' s) (comp r r')
             ≅⟨ ass ⟩
             comp s' (comp s (comp r r'))
             ≅⟨ cong (comp s') (sym ass) ⟩
             comp s' (comp (comp s r) r')
             ≅⟨ cong (λ x → comp s' (comp x r')) l1 ⟩
             comp s' (comp e r')
             ≅⟨ cong (λ x → comp s' (comp x r')) (restRetractionProp sr) ⟩
             comp s' (comp (rest r) r')
             ≅⟨ cong (comp s') R4 ⟩
             comp s' (comp r' (rest (comp r r')))
             ≅⟨ sym ass ⟩
             comp (comp s' r') (rest (comp r r'))
             ≅⟨ cong (λ y → comp y (rest (comp r r'))) l1' ⟩
             comp e' (rest (comp r r'))
             ≅⟨ cong (λ y → comp y (rest (comp r r'))) (restRetractionProp sr') ⟩
             comp (rest r') (rest (comp r r'))
             ≅⟨ R2 ⟩
             comp (rest (comp r r')) (rest r')
             ≅⟨ R3 ⟩
             rest (comp (comp r r') (rest r'))
             ∎)
            (proof
             comp (comp r r') (comp s' s)
             ≅⟨ ass ⟩
             comp r (comp r' (comp s' s))
             ≅⟨ cong (comp r) (sym ass) ⟩
             comp r (comp (comp r' s') s)
             ≅⟨ cong (λ x → comp r (comp x s)) l2' ⟩
             comp r (comp iden s)
             ≅⟨ cong (comp r) idl ⟩
             comp r s
             ≅⟨ l2 ⟩
             iden
             ∎)

pul∈sysSectionsOfRestIdem : ∀{A B C}(f : Tot C B){g : Tot A B} → SectionOfRestIdem g → 
                            Σ (Pullback f g) λ p → SectionOfRestIdem (Square.h (Pullback.sq p))
pul∈sysSectionsOfRestIdem f {g} sr = 
  let open SectionOfRestIdem sr
      t = hom f
      s = hom g
      open Split (restIdemSplit (idem _ (rest (comp e t)) lemii) (sym lemi)) 
                 renaming (B to B'; s to s'; r to r'; splitLaw1 to splitLaw1'; splitLaw2 to splitLaw2')

      s'TotProp : rest s' ≅ iden
      s'TotProp = lemiii (sectionIsMono (restIdemSplit (idem _ (rest (comp e t)) lemii) (sym lemi)))

      k : Hom B' _
      k = comp r (comp t s')

      kTotProp : rest k ≅ iden {B'}
      kTotProp =
        proof
        rest (comp r (comp t s'))
        ≅⟨ cong rest (sym idl) ⟩
        rest (comp iden (comp r (comp t s')))
        ≅⟨ cong (λ y → rest (comp y (comp r (comp t s')))) (sym (totProp g)) ⟩
        rest (comp (rest s) (comp r (comp t s')))
        ≅⟨ sym lemiv ⟩
        rest (comp s (comp r (comp t s')))
        ≅⟨ cong rest (sym ass) ⟩
        rest (comp (comp s r) (comp t s'))
        ≅⟨ cong (λ y → rest (comp y (comp t s'))) splitLaw1 ⟩
        rest (comp e (comp t s'))
        ≅⟨ cong rest (sym ass) ⟩
        rest (comp (comp e t) s')
        ≅⟨ lemiv ⟩
        rest (comp (rest (comp e t)) s')
        ≅⟨ cong (λ y → rest (comp y s')) (sym splitLaw1') ⟩
        rest (comp (comp s' r') s')
        ≅⟨ cong rest ass ⟩
        rest (comp s' (comp r' s'))
        ≅⟨ cong (λ y → rest (comp s' y)) splitLaw2' ⟩
        rest (comp s' iden)
        ≅⟨ cong rest idr ⟩
        rest s'
        ≅⟨ s'TotProp ⟩
        iden
        ∎

      scom : comp t s' ≅ comp s k
      scom = 
        proof 
        comp t s' 
        ≅⟨ sym idr ⟩ 
        comp (comp t s') iden
        ≅⟨ cong (comp (comp t s')) (sym splitLaw2') ⟩ 
        comp (comp t s') (comp r' s')
        ≅⟨ ass ⟩ 
        comp t (comp s' (comp r' s'))
        ≅⟨ cong (comp t) (sym ass) ⟩ 
        comp t (comp (comp s' r') s')
        ≅⟨ cong (λ y → comp t (comp y s')) splitLaw1' ⟩ 
        comp t (comp (rest (comp e t)) s')
        ≅⟨ sym ass ⟩ 
        comp (comp t (rest (comp e t))) s'
        ≅⟨ cong (λ y → comp y s') (sym R4) ⟩ 
        comp (comp (rest e) t) s'
        ≅⟨ cong (λ y → comp (comp y t) s') (sym restIdem) ⟩ 
        comp (comp e t) s'
        ≅⟨ cong (λ y → comp (comp y t) s') (sym splitLaw1) ⟩ 
        comp (comp (comp s r) t) s'
        ≅⟨ ass ⟩ 
        comp (comp s r) (comp t s')
        ≅⟨ ass ⟩ 
        comp s k 
        ∎ 

      sq = square B' (tot s' s'TotProp) (tot k kTotProp) (totEq scom)

      uniqPul : (sq' : Square f g) →
                Σ (SqMap sq' sq) λ u → (u' : SqMap sq' sq) → SqMap.sqMor u ≅ SqMap.sqMor u'
      uniqPul sq' =
        let open Square sq' renaming (h to h'; k to k'; scom to scom')
            x = hom h'
            y = hom k'
            u = comp r' x

            uRightTr : comp k u ≅ y
            uRightTr = sectionIsMono (sectionOfRestIdemSplit sr) 
              (proof
               comp s (comp (comp r (comp t s')) (comp r' x))
               ≅⟨ cong (comp s) ass ⟩
               comp s (comp r (comp (comp t s') (comp r' x)))
               ≅⟨ sym ass ⟩
               comp (comp s r) (comp (comp t s') (comp r' x))
               ≅⟨ cong (λ y → comp y (comp (comp t s') (comp r' x))) splitLaw1 ⟩
               comp e (comp (comp t s') (comp r' x))
               ≅⟨ cong (comp e) ass ⟩
               comp e (comp t (comp s' (comp r' x)))
               ≅⟨ cong (comp e ∘ comp t) (sym ass) ⟩
               comp e (comp t (comp (comp s' r') x))
               ≅⟨ cong (λ y → comp e (comp t (comp y x))) splitLaw1' ⟩
               comp e (comp t (comp (rest (comp e t)) x))
               ≅⟨ sym ass ⟩
               comp (comp e t) (comp (rest (comp e t)) x)
               ≅⟨ sym ass ⟩
               comp (comp (comp e t) (rest (comp e t))) x
               ≅⟨ cong (λ y → comp y x) R1 ⟩
               comp (comp e t) x
               ≅⟨ ass ⟩
               comp e (comp t x)
               ≅⟨ cong (comp e) (cong hom scom') ⟩
               comp e (comp s y)
               ≅⟨ cong (λ z → comp z (comp s y)) (sym splitLaw1) ⟩
               comp (comp s r) (comp s y)
               ≅⟨ ass ⟩
               comp s (comp r (comp s y))
               ≅⟨ cong (comp s) (sym ass) ⟩
               comp s (comp (comp r s) y)
               ≅⟨ cong (λ z → comp s (comp z y)) splitLaw2  ⟩
               comp s (comp iden y)
               ≅⟨ cong (comp s) idl ⟩
               comp s y
               ∎)

            uLeftTr : comp s' u ≅ x
            uLeftTr = 
              proof
              comp s' u
              ≅⟨ sym ass ⟩
              comp (comp s' r') x
              ≅⟨ cong (λ z → comp z x) splitLaw1' ⟩
              comp (rest (comp e t)) x
              ≅⟨ R4 ⟩
              comp x (rest (comp (comp e t) x)) 
              ≅⟨ cong (comp x ∘ rest) ass ⟩
              comp x (rest (comp e (comp t x))) 
              ≅⟨ cong (comp x ∘ rest ∘ comp e) (cong hom scom') ⟩
              comp x (rest (comp e (comp s y))) 
              ≅⟨ cong (λ z → comp x (rest (comp z (comp s y)))) (sym splitLaw1) ⟩
              comp x (rest (comp (comp s r) (comp s y))) 
              ≅⟨ cong (comp x ∘ rest) ass ⟩
              comp x (rest (comp s (comp r (comp s y)))) 
              ≅⟨ cong (comp x ∘ rest ∘ comp s) (sym ass) ⟩
              comp x (rest (comp s (comp (comp r s) y))) 
              ≅⟨ cong (λ z → comp x (rest (comp s (comp z y)))) splitLaw2  ⟩
              comp x (rest (comp s (comp iden y))) 
              ≅⟨ cong (comp x ∘ rest ∘ comp s) idl ⟩
              comp x (rest (comp s y)) 
              ≅⟨ cong (comp x) lemiv ⟩
              comp x (rest (comp (rest s) y)) 
              ≅⟨ cong (λ z → comp x (rest (comp z y))) (totProp g) ⟩
              comp x (rest (comp iden y)) 
              ≅⟨ cong (comp x ∘ rest) idl ⟩
              comp x (rest y) 
              ≅⟨ cong (comp x) (totProp k') ⟩
              comp x iden 
              ≅⟨ idr ⟩
              x
              ∎

            uTotProp : rest u ≅ iden
            uTotProp =
              proof
              rest (comp r' x)
              ≅⟨ cong rest (sym idl) ⟩
              rest (comp iden (comp r' x))
              ≅⟨ cong (λ y → rest (comp y (comp r' x))) (sym s'TotProp) ⟩
              rest (comp (rest s') (comp r' x))
              ≅⟨ sym lemiv ⟩
              rest (comp s' (comp r' x))
              ≅⟨ cong rest uLeftTr ⟩
              rest x
              ≅⟨ totProp h' ⟩
              iden
              ∎

        in sqmap (tot u uTotProp) (totEq uLeftTr) (totEq uRightTr) , 
           λ u' → 
             let open SqMap u'
                 v = hom sqMor
             in totEq (sectionIsMono (restIdemSplit (idem _ (rest (comp e t)) lemii) (sym lemi)) 
                                     (proof comp s' u ≅⟨ uLeftTr ⟩ x ≅⟨ cong hom (sym leftTr) ⟩ comp s' v ∎)) 
  
  in pullback sq uniqPul , 
     sridem (rest (comp e t)) (sym lemi) r' splitLaw1' splitLaw2'

SectionOfRestIdemSys : StableSys Total
SectionOfRestIdemSys = record { 
  ∈sys = SectionOfRestIdem; 
  mono∈sys = mono∈sysSectionsOfRestIdem; 
  iso∈sys = iso∈sysSectionOfRestIdem; 
  comp∈sys = comp∈sysSectionOfRestIdem; 
  pul∈sys = pul∈sysSectionsOfRestIdem}


