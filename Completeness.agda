
open import RestrictionCat

module Completeness (X : SplitRestCat) where

  open import Categories
  open import Relation.Binary.HeterogeneousEquality
  open import Equality
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Function
  open import Data.Product
  open import Functors
  open SplitRestCat X
  open RestCat rcat
  open Cat cat
  open Totals rcat
  open Tot
  open import Stable  
  open import Pullbacks cat
  open Lemmata

  open import MonicClasses X

  open import PartialMaps Total M
  open Idems cat
  open Sections cat
  open Monos cat
  open Isos

  .totcomprest : {A C : Obj}(f : Hom A C) → (sp : Split (record { E = A; e = rest f; law = lemii rcat })) →
                 let open Split sp
                 in rest (comp f s) ≅ iden {B}
  totcomprest f sp = 
    let open Split sp
    in 
      proof
      rest (comp f s)
      ≅⟨ lemiv rcat ⟩
      rest (comp (rest f) s)
      ≅⟨ cong (λ y → rest (comp y s)) (sym law1) ⟩
      rest (comp (comp s r) s)
      ≅⟨ cong rest ass ⟩
      rest (comp s (comp r s))
      ≅⟨ cong (rest ∘ comp s) law2 ⟩
      rest (comp s iden)
      ≅⟨ cong rest idr ⟩
      rest s
      ≅⟨ lemiii rcat (smon s (r , law2)) ⟩
      iden
      ∎ 

  totretract : {A C : Obj}(f : Hom A C) → (sp : Split (record { E = A; e = rest f; law = lemii rcat })) →
                 let open Split sp
                 in rest r ≅ iden {A}
  totretract f sp = 
    let open Split sp
    in 
     proof
      rest r
      ≅⟨ {!!} ⟩
      rest (comp r iden)
      ≅⟨ {!!} ⟩
      rest (comp (rest s) r)
      ≅⟨ {!!} ⟩
      iden
      ∎
 

  Funct : Fun cat Par
  Funct = 
    let open StableSys Total M
    in record { 
      OMap = λ A → A; 
      HMap = λ {A} {C} f → 
        let open Split (rsplit f)
        in record { 
          A' = B; 
          mhom = record { hom = s; tot = lemiii rcat (smon s (r , law2)) }; 
          fhom = record { hom = comp f s; tot = totcomprest f (rsplit f)}; 
          m∈ = record { As = C; fs = f; rs = r; law1s = law1; law2s = law2 } }; 
      fid = λ {A} → 
            let open Split (rsplit (iden {A}))
                
                isos : Iso cat s
                isos = r ,, 
                       (proof
                        comp s r
                        ≅⟨ law1 ⟩
                        rest (iden {A})
                        ≅⟨ lemiii rcat idmono ⟩
                        iden
                        ∎) ,, 
                       law2

                stot : Tot B A
                stot = record { hom = s; tot = lemiii rcat (smon s (r , law2)) }

            in quotient 
              _ 
              _ 
              (record { hom = s; tot = lemiii rcat (smon s (r , law2)) })
              (Iso.inv Total (IsoTot stot isos) ,,
               TotEq _ _ (
                 proof
                 comp s r
                 ≅⟨ law1 ⟩
                 rest (iden {A})
                 ≅⟨ lemiii rcat idmono ⟩
                 iden
                 ∎) ,, 
               TotEq _ _ law2 ) 
              (TotEq _ _ idl) 
              (TotEq _ _ refl);
      fcomp = {!!} }