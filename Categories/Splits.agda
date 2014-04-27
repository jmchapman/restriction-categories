{-# OPTIONS --type-in-type #-}
open import Categories

module Categories.Splits (X : Cat) where
open import Utilities
open Cat X
open import Categories.Idems
open import Categories.Functors


-- Definition of Split(X), which is the category where
-- every idempotent splits

record IdemClass : Set where
  field ∈   : Idem X → Set
        .id∈ : ∀{X} → ∈ (record { E = X; e = iden; law = idl })

record SplitMap (ide ide' : Idem X) : Set where
  open Idem X ide
  open Idem X ide' renaming (E to E' ; e to e' ; law to law')
  field imap : Hom E E'
        .mlaw : comp e' (comp imap e) ≅ imap


.split≅ : {ide ide' : Idem X}(f f' : SplitMap ide ide') →
         SplitMap.imap f ≅ SplitMap.imap f' → f ≅ f'
split≅ {ide}{ide'} f f' p = 
  let open Idem X ide
      open Idem X ide' renaming (E to E'; e to e')
      open SplitMap f
      open SplitMap f' renaming (imap to imap'; mlaw to mlaw') 
  in cong₂ {_} {_} {_}     {Hom E E'}
       {λ imap₁ → comp e' (comp imap₁ e) ≅ imap₁}
       {λ _ _ → SplitMap ide ide'} 
       {imap}
       {imap'}
       (λ (x : Hom E E') y → record { imap = x; mlaw = y })
       p 
       (fixtypes'' p)

.splitprop : {ide ide' : Idem X}(f : SplitMap ide ide') →
            let open SplitMap f
                open Idem X ide
            in comp imap e ≅ imap
splitprop {ide}{ide'} f = 
  let open SplitMap f
      open Idem X ide
      open Idem X ide' renaming (e to e'; law to law')
  in 
    proof
    comp imap e
    ≅⟨ cong (λ y → comp y e) (sym mlaw) ⟩
    comp (comp e' (comp imap e)) e
    ≅⟨ cong (λ y → comp y e) (sym ass) ⟩
    comp (comp (comp e' imap) e) e
    ≅⟨ ass ⟩
    comp (comp e' imap) (comp e e)
    ≅⟨ cong (comp (comp e' imap)) law ⟩
    comp (comp e' imap) e
    ≅⟨ ass ⟩
    comp e' (comp imap e)
    ≅⟨ mlaw ⟩
    imap
    ∎

.splitprop2 : {ide ide' : Idem X}(f : SplitMap ide ide') →
             let open SplitMap f
                 open Idem X ide' renaming (e to e')
             in comp e' imap ≅ imap
splitprop2 {ide}{ide'} f = 
  let open SplitMap f
      open Idem X ide
      open Idem X ide' renaming (e to e'; law to law')
  in 
    proof
    comp e' imap
    ≅⟨ cong (comp e') (sym mlaw) ⟩
    comp e' (comp e' (comp imap e))
    ≅⟨ sym ass ⟩
    comp (comp e' e') (comp imap e)
    ≅⟨ cong (λ y → comp y (comp imap e)) law' ⟩
    comp e' (comp imap e)
    ≅⟨ mlaw ⟩
    imap
    ∎


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

.splitidl : {ide ide' : Idem X}{f : SplitMap ide ide'} → 
           splitcomp splitiden f ≅ f
splitidl {ide}{ide'}{f} = 
  let open SplitMap f
      open Idem X ide
      open Idem X ide' renaming (E to E' ; e to e' ; law to law')
  in split≅  (splitcomp splitiden f) f
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

.splitidr : {ide ide' : Idem X}{f : SplitMap ide ide'} → 
           splitcomp f splitiden ≅ f
splitidr {ide}{ide'}{f} = 
  let open SplitMap f
      open Idem X ide
      open Idem X ide' renaming (E to E' ; e to e' ; law to law')
  in split≅ (splitcomp f splitiden) f
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
    Obj = Σ' (Idem X) ∈;
    Hom = λ {(ide ,, p) (ide' ,, p') → SplitMap ide ide'};
    iden = splitiden;
    comp = splitcomp;
    idl = λ{_}{_}{f} → splitidl {f = f} ;
    idr = λ{_}{_}{f} → splitidr {f = f} ;
    ass = λ{_}{_}{_}{_}{f}{g}{h} → split≅ 
      (splitcomp (splitcomp f g) h)
      (splitcomp f (splitcomp g h))
      ass }


Incl : (E : IdemClass) → Fun X (SplitCat E)
Incl E = 
  let open IdemClass E
  in record { 
    OMap = λ A → 
      record { E = A; e = iden; law = idl } ,, 
      id∈; 
    HMap = λ {A}{B} f → 
      record { 
        imap = f; 
        mlaw = 
          proof
          comp iden (comp f iden)
          ≅⟨ idl ⟩
          comp f iden
          ≅⟨ idr ⟩
          f
          ∎ }; 
    fid = split≅ _ _ refl ;
    fcomp = split≅ _ _ refl }

FaithfulIncl : (E : IdemClass) → Faithful (Incl E)
FaithfulIncl E refl = refl

FullIncl : (E : IdemClass) → Full (Incl E)
FullIncl E {A}{B}{f} = 
  let open SplitMap f
  in imap ,, split≅ _ _ refl

