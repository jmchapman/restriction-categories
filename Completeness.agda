open import SplitRestCats

module Completeness (X : SplitRestCat) where

  open import Categories
  open import RestrictionCat
  open import Relation.Binary.HeterogeneousEquality
  open import Utilities
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Function
  open import Data.Product
  open import Functors
  open import RestrictionFunctors
  open SplitRestCat X
  open RestCat rcat

  open Cat cat
  open import Totals rcat
  open Tot
  open import Stable 
  open import Categories.Pullbacks
  open Lemmata

  open import MonicClasses X

  open import PartialMaps Total M
  open import Soundness Total M
  open import Categories.Idems cat
  open import Categories.Sections cat
  open import Categories.Monos cat
  open import Categories.Isos

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

  HMap1 : ∀{A C}(f : Hom A C) → Span A C
  HMap1 {A}{C} f =
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

  .fid : ∀{A} → HMap1 (iden {A}) ~Span~ idspan {A}
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

      in spaneq
        (record { hom = s; tot = lemiii rcat (smon s (r , law2)) })
        (Iso.inv (IsoTot stot isos) ,,
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

  .fcomp : ∀{A B C}{g : Hom B C}{f : Hom A B} → HMap1 (comp g f) ~Span~ compspan (HMap1 g) (HMap1 f)
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
        open Span (HMap1 f) renaming (mhom to mft; fhom to fmft; m∈ to mf∈)
        open Span (HMap1 g) renaming (mhom to mgt; fhom to gmgt; m∈ to mg∈)

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

        isosplitmap : Σ (Hom Agf W) λ u → Iso cat u
        isosplitmap = lemmamap (record { E = A ; e = rest (comp g f); law = lemii rcat}) 
                               (rsplit (comp g f))
                               fgsplit

        u = proj₁ isosplitmap

        isosplitlaw1 : comp u rgf ≅ comp r' rf
        isosplitlaw1 = lemmalaw1 (record { E = A ; e = rest (comp g f); law = lemii rcat}) 
                                 (rsplit (comp g f))
                                 fgsplit
       
        isosplitlaw2 : comp (comp mf m') u ≅ mgf
        isosplitlaw2 = lemmalaw2 (record { E = A ; e = rest (comp g f); law = lemii rcat}) 
                                 (rsplit (comp g f))
                                 fgsplit

        equat : comp (comp g mg) h ≅ comp (comp g f) (comp mf m')
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
    in spaneq
        (record { hom = u; tot = lemiii rcat (iso→mono cat (proj₂ isosplitmap))})
        (IsoTot (record { hom = u; tot = lemiii rcat (iso→mono cat (proj₂ isosplitmap)) }) (proj₂ isosplitmap)) 
        (TotEq _ _ isosplitlaw2) 
        (TotEq _ 
               _ 
               (proof
                comp (comp (comp g mg) (comp rg (comp (comp f mf) m'))) u
                ≅⟨ cong (λ y → comp y u) equat ⟩
                comp (comp (comp g f) (comp mf m')) u
                ≅⟨ ass ⟩
                comp (comp g f) (comp (comp mf m') u)
                ≅⟨ cong (comp (comp g f)) isosplitlaw2 ⟩
                comp (comp g f) mgf
                ∎
                ))

  Funct : Fun cat Par
  Funct = record { 
    OMap = λ A → A; 
    HMap = abs' ∘ HMap1;
    fid = ax1' _ _ fid;
    fcomp = λ {_}{_}{_}{g}{f} → ax1' 
      _ 
      _ 
      (~trans (fcomp {g = g}{f = f}) (~sym (~cong (ax3' _) (ax3' _))))}

  .frest : ∀{A B}{f : Hom A B} → restp (HMap1 f) ~Span~ HMap1 (rest f)
  frest {A}{B}{f = f} = 
    let open Split (rsplit f) renaming (B to A'; s to m)
        open Split (rsplit (rest f)) renaming (B to A''; s to m'; r to r'; law1 to law1'; law2 to law2')

        ide : Idem
        ide = record { E = A; e = rest f; law = lemii rcat}

        ide' : Idem
        ide' = record { E = A; e = rest (rest f); law = lemii rcat}

        ide≅ide' : ide ≅ ide'
        ide≅ide' = idem≅ refl (sym (lemi rcat))

        umap : Σ (Hom A' A'') (Iso cat)
        umap = lemmamap' ide 
                         ide'
                         ide≅ide'
                         (rsplit f)
                         (rsplit (rest f))

        ulaw1 : comp (proj₁ umap) r ≅ r'
        ulaw1 = lemmalaw1' ide 
                           ide'
                           ide≅ide'
                           (rsplit f)
                           (rsplit (rest f))

        ulaw2 : comp m' (proj₁ umap) ≅ m
        ulaw2 = lemmalaw2' ide 
                           ide'
                           ide≅ide'
                           (rsplit f)
                           (rsplit (rest f))

        eq : comp (comp (rest f) m') (proj₁ umap) ≅ m
        eq = 
          proof
          comp (comp (rest f) m') (proj₁ umap)
          ≅⟨ ass ⟩
          comp (rest f) (comp m' (proj₁ umap))
          ≅⟨ cong (comp (rest f)) ulaw2 ⟩
          comp (rest f) m
          ≅⟨ cong (λ y → comp y m) (sym law1) ⟩
          comp (comp m r) m
          ≅⟨ ass ⟩
          comp m (comp r m)
          ≅⟨ cong (comp m) law2 ⟩
          comp m iden
          ≅⟨ idr ⟩
          m
          ∎

    in spaneq
      (record { hom = proj₁ umap; tot = lemiii rcat (iso→mono cat (proj₂ umap)) }) 
      (IsoTot (record { hom = proj₁ umap; tot = lemiii rcat (iso→mono cat (proj₂ umap))}) (proj₂ umap))
      (TotEq _ _ ulaw2)
      (TotEq _ _ eq)

  RFunct : RestFun rcat RestPartials
  RFunct = record {
    fun = Funct;
    frest = λ {_}{_}{f} → ax1'
      _
      _
      (~trans (Span~restp (ax3' _)) (frest {f = f})) }

  HMap2 : ∀{A C} → Span A C → Hom A C
  HMap2 {A}{C} sp = 
    let open Span sp
        open Tot fhom renaming (hom to g)
        open SRestIde m∈
    in comp g rs

--  postulate HMap2~Span : ∀{A B}{sp sp' : Span A B} → sp ~Span~ sp' → HMap2 sp ≅ HMap2 sp'

  .HMap2~Span : ∀{A B}{sp sp' : Span A B} → sp ~Span~ sp' → HMap2 sp ≅ HMap2 sp'
  HMap2~Span {A}{B}{sp}{sp'} y = --(spaneq iso (inv ,, rinv ,, linv) p q) = 
    let open _~Span~_ y renaming (s to iso)
        open Iso Total siso 
        open Span sp 
        open Span sp' renaming (A' to A''; mhom to mhom'; fhom to fhom'; m∈ to m∈')

        open Tot mhom renaming (hom to m)
        open Tot mhom' renaming (hom to m')
        open Tot fhom renaming (hom to f)
        open Tot fhom' renaming (hom to g)
        open Tot iso renaming (hom to s; tot to st) 
        open Tot inv renaming (hom to s⁻¹)


        open SRestIde m∈ renaming (As to Af; rs to rf; law1s to law1f; law2s to law2f)        
        open SRestIde m∈' renaming (As to Ag; fs to e; rs to rg; law1s to law1g; law2s to law2g)

        seq1 : s ≅ comp rg m
        seq1 = 
          proof 
          s
          ≅⟨ sym idl ⟩
          comp iden s
          ≅⟨ cong (λ y → comp y s) (sym law2g) ⟩
          comp (comp rg m') s
          ≅⟨ ass ⟩
          comp rg (comp m' s)
          ≅⟨ cong (comp rg) (TotEqHom p) ⟩
          comp rg m
          ∎

        seq2 : s⁻¹ ≅ comp rf m'
        seq2 = 
          proof 
          s⁻¹
          ≅⟨ sym idl ⟩
          comp iden s⁻¹
          ≅⟨ cong (λ y → comp y s⁻¹) (sym law2f) ⟩
          comp (comp rf m) s⁻¹
          ≅⟨ ass ⟩
          comp rf (comp m s⁻¹)
          ≅⟨ cong (λ y → comp rf (comp y s⁻¹)) (sym (TotEqHom p)) ⟩
          comp rf (comp (comp m' s) s⁻¹)
          ≅⟨ cong (comp rf) ass ⟩
          comp rf (comp m' (comp s s⁻¹))
          ≅⟨ cong ((comp rf) ∘ (comp m')) (TotEqHom rinv) ⟩
          comp rf (comp m' iden)
          ≅⟨ cong (comp rf) idr ⟩
          comp rf m'
          ∎

        rgeq1 : rg ≅ comp s (comp rf (rest rg))
        rgeq1 = 
          proof
          rg
          ≅⟨ sym idl ⟩
          comp iden rg
          ≅⟨ cong (λ y → comp y rg) (sym (TotEqHom rinv)) ⟩
          comp (comp s s⁻¹) rg
          ≅⟨ ass ⟩
          comp s (comp s⁻¹ rg)
          ≅⟨ cong (λ y → comp s (comp y rg)) seq2 ⟩
          comp s (comp (comp rf m') rg)
          ≅⟨ cong (comp s) ass ⟩
          comp s (comp rf (comp m' rg))
          ≅⟨ cong ((comp s) ∘ (comp rf)) (SRIdeProp m∈') ⟩
          comp s (comp rf (rest rg))
          ∎

        restrgeq : rest rg ≅ comp (rest rg) (rest rf)
        restrgeq = 
          proof
          rest rg
          ≅⟨ cong rest rgeq1 ⟩
          rest (comp s (comp rf (rest rg)))
          ≅⟨ lemiv rcat ⟩ 
          rest (comp (rest s) (comp rf (rest rg)))
          ≅⟨ cong (λ y → rest (comp y (comp rf (rest rg)))) st ⟩
          rest (comp iden (comp rf (rest rg)))
          ≅⟨ cong rest idl ⟩
          rest (comp rf (rest rg))
          ≅⟨ sym R3 ⟩
          comp (rest rf) (rest rg)
          ≅⟨ R2 ⟩
          comp (rest rg) (rest rf)
          ∎

        rgeq2 : rg ≅ comp rg (rest rf)
        rgeq2 = 
          proof
          rg
          ≅⟨ sym R1 ⟩
          comp rg (rest rg)
          ≅⟨ cong (comp rg) restrgeq ⟩
          comp rg (comp (rest rg) (rest rf))
          ≅⟨ sym ass ⟩
          comp (comp rg (rest rg)) (rest rf)
          ≅⟨ cong (λ y → comp y (rest rf)) R1 ⟩
          comp rg (rest rf)
          ∎

    in proof
       comp f rf
       ≅⟨ cong (λ y → comp y rf) (sym (TotEqHom q)) ⟩
       comp (comp g s) rf
       ≅⟨ ass ⟩
       comp g (comp s rf)
       ≅⟨ cong (λ y → comp g (comp y rf)) seq1 ⟩
       comp g (comp (comp rg m) rf)
       ≅⟨ cong (comp g) ass ⟩
       comp g (comp rg (comp m rf))
       ≅⟨ cong ((comp g) ∘ (comp rg)) (SRIdeProp m∈) ⟩
       comp g (comp rg (rest rf))
       ≅⟨ cong (comp g) (sym rgeq2) ⟩
       comp g rg
       ∎


  .fid2 : ∀{A} → HMap2 (rep' (abs' (idspan {A}))) ≅ iden {A}
  fid2 = trans (HMap2~Span (ax3' _)) idl

  .fcomp2' : ∀{A B C}{sp' : Span B C}{sp : Span A B} → HMap2 (compspan sp' sp) ≅ comp (HMap2 sp') (HMap2 sp)
  fcomp2' {A}{B}{C}{sp'}{sp} =
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

  .fcomp2 : ∀{A B C}{q' : Q' {B} {C}}{q : Q' {A} {B}} → HMap2 (rep' (abs' (compspan (rep' q') (rep' q)))) ≅ comp (HMap2 (rep' q')) (HMap2 (rep' q))
  fcomp2 {A}{B}{C}{q'}{q} = trans (HMap2~Span (ax3' _)) (fcomp2' {sp' = rep' q'}{sp = rep' q})

  Funct2 : Fun Par cat
  Funct2 = record {
    OMap = λ A → A; 
    HMap = HMap2 ∘ rep';
    fid = fid2;
    fcomp = fcomp2 }

  open Fun

  .frest2' : ∀{A B}{sp : Span A B} → rest (HMap2 sp) ≅ HMap2 (restp sp)
  frest2' {sp = sp} = 
    let open Span sp renaming (mhom to mp; fhom to fp)
        open Tot mp renaming (hom to m)
        open Tot fp renaming (hom to f; tot to ft)
        open SRestIde m∈ renaming (rs to r)
    in 
      proof
      rest (comp f r)
      ≅⟨ lemiv rcat ⟩
      rest (comp (rest f) r)
      ≅⟨ cong (λ y → rest (comp y r)) ft ⟩
      rest (comp iden r)
      ≅⟨ cong rest idl ⟩
      rest r
      ≅⟨ sym (SRIdeProp m∈) ⟩
      comp m r
      ∎

  .frest2 : ∀{A B}{q : Q' {A} {B}} → rest (HMap2 (rep' q)) ≅ HMap2 (rep' (abs' (restp (rep' q))))
  frest2 {q = q} = trans (frest2' {sp = rep' q}) (HMap2~Span (~sym (ax3' _)))

  RFunct2 : RestFun RestPartials rcat
  RFunct2 = record {
    fun = Funct2;
    frest = frest2 }

-- Iso proof

  .HIso1' : ∀{A C}(sp : Span A C) → HMap1 (HMap2 sp) ~Span~ sp
  HIso1' {A}{C} sp = 
    let open Span sp renaming (mhom to nt; fhom to gt; m∈ to n∈)
        open Tot nt renaming (hom to n)
        open Tot gt renaming (hom to g; tot to gp)

        open SRestIde n∈ renaming (rs to r; law1s to law1; law2s to law2)

        open Span (HMap1 (HMap2 sp)) renaming (A' to A''; mhom to mt)
        open Tot mt renaming (hom to m)

        open SRestIde m∈ renaming (rs to r'; law1s to law1'; law2s to law2')

        spl : Split (record { E = A; e = rest r; law = lemii rcat})
        spl = record { 
          B = A'; 
          s = n; 
          r = r; 
          law1 = SRIdeProp n∈;
          law2 = law2}

        spl' : Split (record { E = A; e = rest r; law = lemii rcat})
        spl' = record { 
          B = A''; 
          s = m; 
          r = r'; 
          law1 = 
            proof
            comp m r'
            ≅⟨ law1' ⟩
            rest (comp g r)
            ≅⟨ lemiv rcat ⟩
            rest (comp (rest g) r)
            ≅⟨ cong (λ y → rest (comp y r)) gp ⟩
            rest (comp iden r)
            ≅⟨ cong rest idl ⟩
            rest r
            ∎;
          law2 = law2'}

        α : Hom A' A''
        α = proj₁ (lemmamap (record { E = A; e = rest r; law = lemii rcat}) spl spl')

        αt : Tot A' A''
        αt = record { 
          hom = α; 
          tot = lemiii rcat (iso→mono cat (proj₂ (lemmamap (record { E = A; e = rest r; law = lemii rcat}) spl spl')))}

        equat : comp (comp (comp g r) m) α ≅ g
        equat = 
          proof
          comp (comp (comp g r) m) α 
          ≅⟨ ass ⟩
          comp (comp g r) (comp m α) 
          ≅⟨ cong (comp (comp g r)) (lemmalaw2 (record { E = A; e = rest r; law = lemii rcat}) spl spl') ⟩
          comp (comp g r) n 
          ≅⟨ ass ⟩
          comp g (comp r n) 
          ≅⟨ cong (comp g) law2 ⟩
          comp g iden
          ≅⟨ idr ⟩
          g
          ∎

    in ~sym (spaneq
                αt 
                (IsoTot αt (proj₂ (lemmamap (record { E = A; e = rest r; law = lemii rcat}) spl spl')))
                (TotEq _ nt (lemmalaw2 (record { E = A; e = rest r; law = lemii rcat}) spl spl'))
                (TotEq _ gt equat))

  .HIso1 : ∀{A C}(q : Q' {A} {C}) → abs' (HMap1 (HMap2 (rep' q))) ≅ q
  HIso1 {A}{C} q = trans (ax1' _ _ (HIso1' (rep' q))) (ax2' q)

  .HIso2' : ∀{A C}(f : Hom A C) → HMap2 (HMap1 f) ≅ f
  HIso2' {A}{C} f = 
    let open Split (rsplit f)
    in 
      proof
      comp (comp f s) r
      ≅⟨ ass ⟩
      comp f (comp s r)
      ≅⟨ cong (comp f) law1 ⟩
      comp f (rest f)
      ≅⟨ R1 ⟩
      f
      ∎

  .HIso2 : ∀{A C}(f : Hom A C) → HMap2 (rep' (abs' (HMap1 f))) ≅ f
  HIso2 f = trans (HMap2~Span (ax3' _)) (HIso2' f)

  IsoCompl : Iso CCat Funct
  IsoCompl = Funct2 ,, 
             Fun≅ refl HIso1 ,, 
             Fun≅ refl HIso2

  RIsoCompl : Iso RCCat RFunct
  RIsoCompl = RFunct2 ,, 
              RFun≅ (Fun≅ refl HIso1) ,, 
              RFun≅ (Fun≅ refl HIso2)

