{-# OPTIONS --type-in-type #-}
open import Categories

module Splits (X : Cat) where

open import Relation.Binary.HeterogeneousEquality
open import Equality
open ≅-Reasoning renaming (begin_ to proof_)
open import Data.Product
open Cat X
open Idems


-- Definition of Split(X), which is the category where
-- every idempotent splits

record IdemClass : Set where
  field ∈   : Idem X → Set
        id∈ : ∀{X} → ∈ (record { E = X; e = iden; law = idl })

record SplitMap (ide ide' : Idem X) : Set where
  open Idem X ide
  open Idem X ide' renaming (E to E' ; e to e' ; law to law')
  field imap : Hom E E'
        mlaw : comp e' (comp imap e) ≅ imap

split≅ : {ide ide' : Idem X}{f f' : SplitMap ide ide'} →
         SplitMap.imap f ≅ SplitMap.imap f' → f ≅ f'
split≅ {ide}{ide'}{f}{f'} p = 
  let open Idem X ide
      open Idem X ide' renaming (E to E'; e to e')
      open SplitMap f
      open SplitMap f' renaming (imap to imap'; mlaw to mlaw') 
  in cong₂ {_} {_} {_} {Hom E E'}
       {λ imap₁ → comp e' (comp imap₁ e) ≅ imap₁}
       {λ _ _ → SplitMap ide ide'} (λ x y → record { imap = x; mlaw = y })
       p 
       (fixtypes 
         (proof 
          comp e' (comp imap e) 
          ≅⟨ mlaw ⟩ 
          imap
          ≅⟨ p ⟩ 
          imap'
          ≅⟨ sym mlaw' ⟩ 
          comp e' (comp imap' e) 
          ∎)
         p)

splitiden : {ide : Idem X} → SplitMap ide ide
splitiden {ide} = 
  let open Idem X ide
  in record { 
    imap = e; 
    mlaw = 
      proof 
      comp e (comp e e) 
      ≅⟨ cong (comp e) law ⟩ 
      comp e e
      ≅⟨ law ⟩ 
      e 
      ∎}

splitcomp : {ide ide' ide'' : Idem X} (f' : SplitMap ide' ide'') →
            (f : SplitMap ide ide') → SplitMap ide ide''
splitcomp {ide}{ide'}{ide''} f' f = 
  let open SplitMap f
      open SplitMap f' renaming (imap to imap' ; mlaw to mlaw')
      open Idem X ide
      open Idem X ide' renaming (E to E' ; e to e' ; law to law')
      open Idem X ide'' renaming (E to E'' ; e to e'' ; law to law'')
  in record { 
       imap = comp imap' imap; 
       mlaw = 
       proof
         comp e'' (comp (comp imap' imap) e)
         ≅⟨ cong (comp e'') ass ⟩
         comp e'' (comp imap' (comp imap e))
         ≅⟨ sym ass ⟩
         comp (comp e'' imap') (comp imap e)
         ≅⟨ cong (λ y → comp (comp e'' y) (comp imap e)) (sym mlaw') ⟩
         comp (comp e'' (comp e'' (comp imap' e'))) (comp imap e)
         ≅⟨ cong (λ y → comp y (comp imap e)) (sym ass) ⟩
         comp (comp (comp e'' e'') (comp imap' e')) (comp imap e)
         ≅⟨ cong (λ y → comp (comp y (comp imap' e')) (comp imap e)) law'' ⟩
         comp (comp e'' (comp imap' e')) (comp imap e)
         ≅⟨ cong (λ y → comp y (comp imap e)) mlaw' ⟩
         comp imap' (comp imap e)
         ≅⟨ cong (λ y → comp imap' (comp y e)) (sym mlaw) ⟩
         comp imap' (comp (comp e' (comp imap e)) e)
         ≅⟨ cong (λ y → comp imap' (comp y e)) (sym ass) ⟩
         comp imap' (comp (comp (comp e' imap) e) e)
         ≅⟨ cong (comp imap') ass ⟩
         comp imap' (comp (comp e' imap) (comp e e))
         ≅⟨ cong (λ y → comp imap' (comp (comp e' imap) y)) law ⟩
         comp imap' (comp (comp e' imap) e)
         ≅⟨ cong (comp imap') ass ⟩
         comp imap' (comp e' (comp imap e))
         ≅⟨ cong (comp imap') mlaw ⟩
         comp imap' imap
         ∎ } 

splitidl : {ide ide' : Idem X}{f : SplitMap ide ide'} → 
           splitcomp splitiden f ≅ f
splitidl {ide}{ide'}{f} = 
  let open SplitMap f
      open Idem X ide
      open Idem X ide' renaming (E to E' ; e to e' ; law to law')
  in split≅ 
     (proof 
      comp e' imap 
      ≅⟨ cong (comp e') (sym mlaw) ⟩ 
      comp e' (comp e' (comp imap e))
      ≅⟨ sym ass ⟩ 
      comp (comp e' e') (comp imap e)
      ≅⟨ cong (λ y → comp y (comp imap e)) law' ⟩ 
      comp e' (comp imap e) 
      ≅⟨ mlaw ⟩ 
      imap 
      ∎)

splitidr : {ide ide' : Idem X}{f : SplitMap ide ide'} → 
           splitcomp f splitiden ≅ f
splitidr {ide}{ide'}{f} = 
  let open SplitMap f
      open Idem X ide
      open Idem X ide' renaming (E to E' ; e to e' ; law to law')
  in split≅ 
     (proof 
      comp imap e
      ≅⟨ cong (λ y → comp y e) (sym mlaw) ⟩ 
      comp (comp e' (comp imap e)) e 
      ≅⟨ ass ⟩ 
      comp e' (comp (comp imap e) e)
      ≅⟨ cong (comp e') ass ⟩ 
      comp e' (comp imap (comp e e))
      ≅⟨ cong (λ y → comp e' (comp imap y)) law ⟩ 
      comp e' (comp imap e)
      ≅⟨ mlaw ⟩ 
      imap 
      ∎)

SplitCat : IdemClass → Cat
SplitCat E = 
  let open IdemClass E
  in record {
    Obj = Σ (Idem X) ∈;
    Hom = λ {(ide , p) (ide' , p') → SplitMap ide ide'};
    iden = splitiden;
    comp = splitcomp;
    idl = splitidl;
    idr = splitidr;
    ass = split≅ ass }



idemsplit : ∀(ide : Idem X)(E : IdemClass) → 
            let open IdemClass E
            in ∈ ide → Idem (SplitCat E)
idemsplit ide E p = record { 
  E = (ide , p); 
  e = splitiden; 
  law = splitidl }

everysplit : ∀(ide : Idem X)(E : IdemClass) → 
             let open IdemClass E
             in (p : ∈ ide) → Split (SplitCat E) (idemsplit ide E p)
everysplit ide E p = record { 
    B = (ide , p); 
    s = splitiden; 
    r = splitiden; 
    law1 = splitidl; 
    law2 = splitidl }
