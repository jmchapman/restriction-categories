
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
  open import Pullbacks
  open Lemmata

  open import MonicClasses X

  open import PartialMaps Total M
  open Idems cat
  open Sections cat
  open Monos cat
  open Isos


-- Functor definition

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

  HMap : ∀{A C}(f : Hom A C) → Span A C
  HMap {A}{C} f =
    let open Split (rsplit f)

        mhom : Tot B A
        mhom = record { hom = s; tot = lemiii rcat (smon s (r , law2)) }
  
        fhom : Tot B C
        fhom = record { hom = comp f s; tot = totcomprest f (rsplit f)}

        m∈ : SRestIde mhom
        m∈ = record { As = C; fs = f; rs = r; law1s = law1; law2s = law2 }

    in record { 
      A' = B; 
      mhom = mhom;
      fhom = fhom;
      m∈ = m∈ }

  .fid : ∀{A} → HMap (iden {A}) ≅ idspan {A}
  fid {A} = 
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
        (TotEq _ _ refl)

  .fcomp : ∀{A B C}{g : Hom B C}{f : Hom A B} → HMap (comp g f) ≅ compspan (HMap g) (HMap f)
  fcomp {A}{B}{C}{g}{f} = 
    let open Split (rsplit f) renaming (B to Af; 
                                        s to mf; 
                                        r to rf; 
                                        law1 to law1f;
                                        law2 to law2f)
        open Split (rsplit g) renaming (B to Ag; 
                                        s to mg; 
                                        r to rg; 
                                        law1 to law1g;
                                        law2 to law2g)
        open Split (rsplit (comp g f)) renaming (B to Agf; 
                                        s to mgf; 
                                        r to rgf; 
                                        law1 to law1gf;
                                        law2 to law2gf)
        open Span (HMap f) renaming (mhom to mft; fhom to fmft; m∈ to mf∈)
        open Span (HMap g) renaming (mhom to mgt; fhom to gmgt; m∈ to mg∈)

        open Pullback Total (proj₁ (MXpul fmft mg∈))
        open Square Total sq renaming (h to mt'; k to ht)
        open SRestIde (proj₂ (MXpul fmft mg∈)) renaming (rs to r')

        open Tot mt' renaming (hom to m'; tot to mp')
        open Tot fmft renaming (hom to fmf; tot to fmfp')
        open Tot ht renaming (hom to h; tot to hp)

        .law1gf : comp (comp mf m') (comp r' rf) ≅ rest (comp g f)
        law1gf = 
          proof
          comp (comp mf m') (comp r' rf)
          ≅⟨ ass ⟩
          comp mf (comp m' (comp r' rf))
          ≅⟨ cong (comp mf) (sym ass) ⟩
          comp mf (comp (comp m' r') rf)
          ≅⟨ cong (λ y → comp mf (comp y rf)) (Split.law1 (rsplit (comp (rest g) (comp f mf)))) ⟩
          comp mf (comp (rest (comp (rest g) (comp f mf))) rf)
          ≅⟨ cong (λ y → comp mf (comp y rf)) (sym (lemiv rcat)) ⟩
          comp mf (comp (rest (comp g (comp f mf))) rf)
          ≅⟨ cong (λ y → comp mf (comp (rest y) rf)) (sym ass) ⟩
          comp mf (comp (rest (comp (comp g f) mf)) rf)
          ≅⟨ sym ass ⟩
          comp (comp mf (rest (comp (comp g f) mf))) rf
          ≅⟨ cong (λ y → comp y rf) (sym R4) ⟩
          comp (comp (rest (comp g f)) mf) rf
          ≅⟨ ass ⟩
          comp (rest (comp g f)) (comp  mf rf)
          ≅⟨ cong (comp (rest (comp g f))) law1f ⟩
          comp (rest (comp g f)) (rest f)
          ≅⟨ R3 ⟩
          rest (comp (comp g f) (rest f))
          ≅⟨ cong rest ass ⟩
          rest (comp g (comp f (rest f)))
          ≅⟨ cong (rest ∘ comp g) R1 ⟩
          rest (comp g f)
          ∎

        .law2gf : comp (comp r' rf) (comp mf m') ≅ iden {W}
        law2gf =
          proof 
          comp (comp r' rf) (comp mf m')
          ≅⟨ ass ⟩
          comp r' (comp rf (comp mf m'))
          ≅⟨ cong (comp r') (sym ass) ⟩
          comp r' (comp (comp rf mf) m')
          ≅⟨ cong (λ y → comp r' (comp y m')) law2f ⟩
          comp r' (comp iden m')
          ≅⟨ cong (comp r') idl ⟩
          comp r' m'
          ≅⟨ Split.law2 (rsplit (comp (rest g) (comp f mf))) ⟩
          iden
          ∎

        fgsplit : Split (record { E = A ; e = rest (comp g f); law = lemii rcat})
        fgsplit = record { B = W; s = comp mf m'; r = comp r' rf; law1 = law1gf; law2 = law2gf }

        isosplit : Σ (Hom Agf W) λ u → Iso cat u × (comp u rgf ≅ comp r' rf) × comp (comp mf m') u ≅ mgf
        isosplit = lemma (record { E = A ; e = rest (comp g f); law = lemii rcat}) 
                         (rsplit (comp g f))
                         fgsplit

        u = proj₁ isosplit

{-
        .equat : comp (comp g mg) h ≅ comp (comp g f) (comp mf m')
        equat = 
          proof
          comp (comp g mg) h
          ≅⟨ refl ⟩
          comp (comp g mg) (comp rg (comp (comp f mf) m'))
          ≅⟨ ass ⟩
          comp g (comp mg (comp rg (comp (comp f mf) m')))
          ≅⟨ cong (comp g) (sym ass) ⟩
          comp g (comp (comp mg rg) (comp (comp f mf) m'))
          ≅⟨ cong (λ y → comp g (comp y (comp (comp f mf) m'))) law1g ⟩
          comp g (comp (rest g) (comp (comp f mf) m'))
          ≅⟨ sym ass ⟩
          comp (comp g (rest g)) (comp (comp f mf) m')
          ≅⟨ cong (λ y → comp y (comp (comp f mf) m')) R1 ⟩
          comp g (comp (comp f mf) m')
          ≅⟨ cong (comp g) ass ⟩
          comp g (comp f (comp mf m'))
          ≅⟨ sym ass ⟩
          comp (comp g f) (comp mf m')
          ∎
-}

    in quotient _ 
                _ 
                (record { hom = u; tot = lemiii rcat (iso→mono cat (proj₁ (proj₂ isosplit)) )})
                (IsoTot (record { hom = u; tot = lemiii rcat (iso→mono cat (proj₁ (proj₂ isosplit))) }) (proj₁ (proj₂ isosplit))) 
                (TotEq _ _ (proj₂ (proj₂ (proj₂ isosplit)))) 
                (TotEq _ 
                       _ 
                       (proof

                        comp (comp (comp g mg) (comp rg (comp (comp f mf) m'))) u
                        ≅⟨ cong (λ y → comp y u) ass ⟩

                        comp (comp g (comp mg (comp rg (comp (comp f mf) m')))) u
                        ≅⟨ cong (λ y → comp (comp g y) u) (sym ass) ⟩
                        comp (comp g (comp (comp mg rg) (comp (comp f mf) m'))) u
                        ≅⟨ cong (λ y → comp (comp g (comp y (comp (comp f mf) m'))) u) law1g ⟩
                        comp (comp g (comp (rest g) (comp (comp f mf) m'))) u
                        ≅⟨ cong (λ y → comp y u) (sym ass) ⟩
                        comp (comp (comp g (rest g)) (comp (comp f mf) m')) u
                        ≅⟨ cong (λ y → comp (comp y (comp (comp f mf) m')) u) R1 ⟩
                        comp (comp g (comp (comp f mf) m')) u
                        ≅⟨ cong (λ y → comp (comp g y) u) ass ⟩
                        comp (comp g (comp f (comp mf m'))) u
                        ≅⟨ cong (λ y → comp y u) (sym ass) ⟩

                        comp (comp (comp g f) (comp mf m')) u
                        ≅⟨ ass ⟩
                        comp (comp g f) (comp (comp mf m') u)
                        ≅⟨ cong (comp (comp g f)) (proj₂ (proj₂ (proj₂ isosplit))) ⟩
                        comp (comp g f) mgf
                        ∎
                        ))

  Funct : Fun cat Par
  Funct = record { 
    OMap = λ A → A; 
    HMap = HMap;
    fid = fid;
    fcomp = fcomp}

  HMap2 : ∀{A C} → Span A C → Hom A C
  HMap2 {A}{C} sp = 
    let open Span sp
        open Tot fhom renaming (hom to g)
        open SRestIde m∈
    in comp g rs

  .fid2 : ∀{A} → HMap2 (idspan {A}) ≅ iden {A}
  fid2 {A} = idl

  .fcomp2 : ∀{A B C}{sp' : Span B C}{sp : Span A B} → HMap2 (compspan sp' sp) ≅ comp (HMap2 sp') (HMap2 sp)
  fcomp2 {A}{B}{C}{sp'}{sp} =
    let open Span sp 
        open Span sp' renaming (A' to A''; mhom to mhom'; fhom to fhom'; m∈ to m∈')
        open Span (compspan sp' sp) renaming (A' to A'''; mhom to mhom''; fhom to fhom''; m∈ to m∈'')

        open Tot mhom renaming (hom to mf)
        open Tot mhom' renaming (hom to mg)
        open Tot mhom'' renaming (hom to mfm')
        open Tot fhom renaming (hom to f)
        open Tot fhom' renaming (hom to g)
        open Tot fhom'' renaming (hom to gh)

        open SRestIde m∈ renaming (rs to rf)        
        open SRestIde m∈' renaming (fs to e; rs to rg; law1s to law1g; law2s to law2g)        
        open SRestIde m∈'' renaming (rs to r'rf)        

        open Pullback Total (proj₁ (MXpul fhom m∈'))
        open Square Total sq renaming (h to mt'; k to ht)
        open SRestIde (proj₂ (MXpul fhom m∈')) renaming (fs to u; rs to r'; law1s to law1')

        open Tot mt' renaming (hom to m'; tot to mp')
        open Tot ht renaming (hom to h; tot to hp)

    in 
      proof 
      comp gh r'rf 
      ≅⟨ refl ⟩ 
      comp (comp g h) r'rf 
      ≅⟨ refl ⟩ 
      comp (comp g (comp rg (comp f m'))) r'rf 
      ≅⟨ refl ⟩ 
      comp (comp g (comp rg (comp f m'))) (comp r' rf) 
      ≅⟨ sym ass ⟩
      comp (comp (comp g (comp rg (comp f m'))) r') rf
      ≅⟨ cong (λ y → comp y rf) ass ⟩ 
      comp (comp g (comp (comp rg (comp f m')) r')) rf
      ≅⟨ cong (λ y → comp (comp g y) rf) ass ⟩ 
      comp (comp g (comp rg (comp (comp f m') r'))) rf
      ≅⟨ cong (λ y → comp (comp g (comp rg y)) rf) ass ⟩ 
      comp (comp g (comp rg (comp f (comp m' r')))) rf
      ≅⟨ cong (λ y → comp (comp g (comp rg (comp f y))) rf) law1' ⟩
      comp (comp g (comp rg (comp f (rest (comp (rest e) f))))) rf
      ≅⟨ cong (λ y → comp (comp g (comp rg y)) rf) (sym R4) ⟩
      comp (comp g (comp rg (comp (rest (rest e)) f))) rf
      ≅⟨ cong (λ y → comp (comp g (comp rg (comp y f))) rf) (lemi rcat) ⟩
      comp (comp g (comp rg (comp (rest e) f))) rf
      ≅⟨ cong (λ y → comp (comp g (comp rg (comp y f))) rf) (sym law1g) ⟩
      comp (comp g (comp rg (comp (comp mg rg) f))) rf
      ≅⟨ cong (λ y → comp (comp g (comp rg y)) rf) ass ⟩
      comp (comp g (comp rg (comp mg (comp rg f)))) rf
      ≅⟨ cong (λ y → comp (comp g y) rf) (sym ass) ⟩
      comp (comp g (comp (comp rg mg) (comp rg f))) rf
      ≅⟨ cong (λ y → comp (comp g (comp y (comp rg f))) rf) law2g ⟩
      comp (comp g (comp iden (comp rg f))) rf
      ≅⟨ cong (λ y → comp (comp g y) rf) idl ⟩
      comp (comp g (comp rg f)) rf
      ≅⟨ cong (λ y → comp y rf) (sym ass) ⟩
      comp (comp (comp g rg) f) rf
      ≅⟨ ass ⟩
      comp (comp g rg) (comp f rf) 
      ∎

{-
  Funct2 : Fun Par cat
  Funct2 = record {
    OMap = λ A → A; 
    HMap = HMap2;
    fid = fid2;
    fcomp = fcomp2}
-}


