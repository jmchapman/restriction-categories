{-# OPTIONS --type-in-type #-}
open import Categories

module Categories.Idems (X : Cat) where

open import Utilities
open Cat X
open import Categories.Functors

record Idem : Set where
  constructor idem
  field E       : Obj
        e       : Hom E E
        idemLaw : comp e e ≅ e

idIdem : {X : Obj} → Idem
idIdem {X} = idem X iden idl

idemEq : ∀{E E' e e' p p'} → E ≅ E' → e ≅ e' → 
         idem E e p ≅ idem E' e' p'
idemEq refl refl = cong (idem _ _) (proof-irr _ _)

record IdemClass : Set where
  field ∈class   : Idem → Set
        id∈class : ∀{X} → ∈class (idIdem {X})

record IdemMor (i i' : Idem) : Set where
  constructor idemmor
  open Idem i
  open Idem i' renaming (E to E' ; e to e')
  field imap    : Hom E E'
        imapLaw : comp e' (comp imap e) ≅ imap

idemMorPrecomp : {i i' : Idem}(f : IdemMor i i') →
                 comp (IdemMor.imap f) (Idem.e i) ≅ IdemMor.imap f
idemMorPrecomp {i}{i'} f = 
  let open IdemMor f
      open Idem i
      open Idem i' renaming (e to e'; idemLaw to idemLaw')
  in 
    proof
    comp imap e
    ≅⟨ cong (λ y → comp y e) (sym imapLaw) ⟩
    comp (comp e' (comp imap e)) e
    ≅⟨ cong (λ y → comp y e) (sym ass) ⟩
    comp (comp (comp e' imap) e) e
    ≅⟨ ass ⟩
    comp (comp e' imap) (comp e e)
    ≅⟨ cong (comp (comp e' imap)) idemLaw ⟩
    comp (comp e' imap) e
    ≅⟨ ass ⟩
    comp e' (comp imap e)
    ≅⟨ imapLaw ⟩
    imap
    ∎

idemMorPostcomp : {i i' : Idem}(f : IdemMor i i') →
                  comp (Idem.e i') (IdemMor.imap f) ≅ IdemMor.imap f
idemMorPostcomp {i}{i'} f = 
  let open IdemMor f
      open Idem i
      open Idem i' renaming (e to e'; idemLaw to idemLaw')
  in 
    proof
    comp e' imap
    ≅⟨ cong (comp e') (sym imapLaw) ⟩
    comp e' (comp e' (comp imap e))
    ≅⟨ sym ass ⟩
    comp (comp e' e') (comp imap e)
    ≅⟨ cong (λ y → comp y (comp imap e)) idemLaw' ⟩
    comp e' (comp imap e)
    ≅⟨ imapLaw ⟩
    imap
    ∎

idemMorEq : ∀{i i' f f' p p'} → f ≅ f' → 
            idemmor {i = i}{i'} f p ≅ idemmor {i = i}{i'} f' p'
idemMorEq refl = cong (idemmor _) (hirL refl) 

idemMorEqProj : {i i' : Idem}{f g : IdemMor i i'} → f ≅ g → IdemMor.imap f ≅ IdemMor.imap g
idemMorEqProj refl = refl

idIdemMor : {i : Idem} → IdemMor i i
idIdemMor {idem _ e p} = record {
  imap = e; 
  imapLaw = 
    proof 
    comp e (comp e e) 
    ≅⟨ cong (comp e) p ⟩ 
    comp e e
    ≅⟨ p ⟩ 
    e 
    ∎}

compIdemMor : {i i' i'' : Idem}(f' : IdemMor i' i'')
              (f : IdemMor i i') → IdemMor i i''
compIdemMor {idem _ e l}{idem _ e' _}{idem _ e'' l''} (idemmor g q) (idemmor f p) = 
  idemmor (comp g f) 
          (proof
           comp e'' (comp (comp g f) e)
           ≅⟨ cong (comp e'') ass ⟩
           comp e'' (comp g (comp f e))
           ≅⟨ sym ass ⟩
           comp (comp e'' g) (comp f e)
           ≅⟨ cong (λ y → comp (comp e'' y) (comp f e)) (sym q) ⟩
           comp (comp e'' (comp e'' (comp g e'))) (comp f e)
           ≅⟨ cong (λ y → comp y (comp f e)) (sym ass) ⟩
           comp (comp (comp e'' e'') (comp g e')) (comp f e)
           ≅⟨ cong (λ y → comp (comp y (comp g e')) (comp f e)) l'' ⟩
           comp (comp e'' (comp g e')) (comp f e)
           ≅⟨ cong (λ y → comp y (comp f e)) q ⟩
           comp g (comp f e)
           ≅⟨ cong (λ y → comp g (comp y e)) (sym p) ⟩
           comp g (comp (comp e' (comp f e)) e)
           ≅⟨ cong (λ y → comp g (comp y e)) (sym ass) ⟩
           comp g (comp (comp (comp e' f) e) e)
           ≅⟨ cong (comp g) ass ⟩
           comp g (comp (comp e' f) (comp e e))
           ≅⟨ cong (λ y → comp g (comp (comp e' f) y)) l ⟩
           comp g (comp (comp e' f) e)
           ≅⟨ cong (comp g) ass ⟩
           comp g (comp e' (comp f e))
           ≅⟨ cong (comp g) p ⟩
           comp g f
           ∎)
           
-- idlIdemMor : {i i' : Idem}{f : IdemMor i i'} → compIdemMor idIdemMor f ≅ f
-- idlIdemMor {i}{i'}{f} = 
--   let open IdemMor f
--       open Idem i
--       open Idem i' renaming (e to e' ; idemLaw to idemLaw')
--   in 
--     idemMorEq
--       (proof 
--        comp e' imap 
--        ≅⟨ cong (comp e') (sym imapLaw) ⟩ 
--        comp e' (comp e' (comp imap e))
--        ≅⟨ sym ass ⟩ 
--        comp (comp e' e') (comp imap e)
--        ≅⟨ cong (λ y → comp y (comp imap e)) idemLaw' ⟩ 
--        comp e' (comp imap e) 
--        ≅⟨ imapLaw ⟩ 
--        imap 
--        ∎)

-- idrIdemMor : {i i' : Idem}{f : IdemMor i i'} → compIdemMor f idIdemMor ≅ f
-- idrIdemMor {i}{i'}{f} = 
--   let open IdemMor f
--       open Idem i
--       open Idem i' renaming (e to e'; idemLaw to idemLaw')
--   in 
--     idemMorEq 
--       (proof 
--        comp imap e
--        ≅⟨ cong (λ y → comp y e) (sym imapLaw) ⟩ 
--        comp (comp e' (comp imap e)) e 
--        ≅⟨ ass ⟩ 
--        comp e' (comp (comp imap e) e)
--        ≅⟨ cong (comp e') ass ⟩ 
--        comp e' (comp imap (comp e e))
--        ≅⟨ cong (λ y → comp e' (comp imap y)) idemLaw ⟩ 
--        comp e' (comp imap e)
--        ≅⟨ imapLaw ⟩ 
--        imap 
--        ∎)

SplitCat : IdemClass → Cat
SplitCat E = 
  let open IdemClass E
  in record {
    Obj  = Σ Idem ∈class;
    Hom  = λ {(i , _) (i' , _) → IdemMor i i'};
    iden = idIdemMor;
    comp = compIdemMor;
    idl  = λ {_}{_}{f} → idemMorEq (idemMorPostcomp f);
    idr  = λ {_}{_}{f} → idemMorEq (idemMorPrecomp f);
    ass  = idemMorEq ass }

InclSplitCat : (E : IdemClass) → Fun X (SplitCat E)
InclSplitCat E = 
  let open IdemClass E
  in record { 
    OMap  = λ A → idem A iden idl , id∈class; 
    HMap  = λ f → 
      idemmor f 
              (proof
               comp iden (comp f iden)
               ≅⟨ idl ⟩
               comp f iden
               ≅⟨ idr ⟩
               f
               ∎); 
    fid   = idemMorEq refl ;
    fcomp = idemMorEq refl }

FullInclSplitCat : {E : IdemClass} → Full (InclSplitCat E)
FullInclSplitCat {f = idemmor f _} = f , idemMorEq refl

FaithfulInclSplitCat : {E : IdemClass} → Faithful (InclSplitCat E)
FaithfulInclSplitCat refl = refl
