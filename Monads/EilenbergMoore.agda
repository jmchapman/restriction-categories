
open import Categories
open import Monads

module Monads.EilenbergMoore (C : Cat)(Tm : Monad C) where

open import Modules C Tm
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Function

open Cat C
open Monad Tm

miden : ∀{X} → ModuleMap X X
miden {X} = 
  let open Module X
  in record { 
    mhom = iden; 
    mcom = 
      proof
      comp iden ν
      ≅⟨ idl ⟩
      ν
      ≅⟨ sym idr ⟩
      comp ν iden
      ≅⟨ cong (comp ν) (sym law1) ⟩
      comp ν (bind η)
      ≅⟨ cong (comp ν ∘ bind) (sym idr) ⟩
      comp ν (bind (comp η iden))
      ∎}

mcomp : ∀{X Y Z} → ModuleMap Y Z → ModuleMap X Y → ModuleMap X Z
mcomp {X}{Y}{Z} f g = 
  let open Module X renaming (ν to νM)
      open Module Y renaming (ν to νN)
      open Module Z renaming (ν to νO)
      open ModuleMap f renaming (mhom to fhom; mcom to fcom)
      open ModuleMap g renaming (mhom to ghom; mcom to gcom)
  in record { 
    mhom = comp fhom ghom; 
    mcom = 
      proof
      comp (comp fhom ghom) νM
      ≅⟨ ass ⟩
      comp fhom (comp ghom νM)
      ≅⟨ cong (comp fhom) gcom ⟩
      comp fhom (comp νN (bind (comp η ghom)))
      ≅⟨ sym ass ⟩
      comp (comp fhom νN) (bind (comp η ghom))
      ≅⟨ cong (λ y → comp y (bind (comp η ghom))) fcom ⟩
      comp (comp νO (bind (comp η fhom))) (bind (comp η ghom))
      ≅⟨ ass ⟩
      comp νO (comp (bind (comp η fhom)) (bind (comp η ghom)))
      ≅⟨ cong (comp νO) (sym law3) ⟩
      comp νO (bind (comp (bind (comp η fhom)) (comp η ghom)))
      ≅⟨ cong (λ y → comp νO (bind y)) (sym ass) ⟩
      comp νO (bind (comp (comp (bind (comp η fhom)) η) ghom))
      ≅⟨ cong (λ y → comp νO (bind (comp y ghom))) law2 ⟩
      comp νO (bind (comp (comp η fhom) ghom))
      ≅⟨ cong (λ y → comp νO (bind y)) ass ⟩
      comp νO (bind (comp η (comp fhom ghom)))
      ∎}

.midl : ∀{X Y}{f : ModuleMap X Y} → mcomp miden f ≅ f
midl {f = f} = ModuleMapEq (mcomp miden f) f idl

.midr : ∀{X Y}{f : ModuleMap X Y} → mcomp f miden ≅ f
midr {f = f} = ModuleMapEq (mcomp f miden) f idr

.mass : ∀{W X Y Z}{f : ModuleMap Y Z}{g : ModuleMap X Y}{h : ModuleMap W X} → 
        mcomp (mcomp f g) h ≅ mcomp f (mcomp g h)
mass {f = f}{g = g}{h = h} = ModuleMapEq (mcomp (mcomp f g) h) 
                                         (mcomp f (mcomp g h))
                                         ass

EM : Cat
EM = record {
  Obj = Module;
  Hom = ModuleMap;
  iden = miden;
  comp = mcomp;
  idl = λ {_}{_}{f} → midl {f = f};
  idr = λ {_}{_}{f} → midr {f = f};
  ass = λ {_}{_}{_}{_}{f}{g}{h} → mass {f = f}{g = g}{h = h}}
