{-# OPTIONS --type-in-type #-}
open import Restriction.SplitRestCats

module Completeness (X : SplitRestCat) where

open import Utilities
open import Categories
open import Restriction.Cat
open import Categories.Functors
open import Restriction.Functors
open SplitRestCat X
open RestCat rcat
open Cat cat
open import Restriction.Totals rcat
open import PartialMaps.Stable 
open import Categories.Pullbacks
open Lemmata rcat
open import PartialMaps.MonicClasses X
open import PartialMaps.Cat Total SectionsOfRestIdem
open import Soundness Total SectionsOfRestIdem
open import Categories.Idems cat
open import Categories.Splits cat
open import Categories.Monos cat
open import Categories.Isos
open import Restriction.Idems rcat
open import Restriction.SplitCatIsRestCat rcat

restIdemIdemGen : ∀{A C}(f : Hom A C) → Idem
restIdemIdemGen f = idem _ (rest f) lemii

restIdemSplitGen : ∀{A C}(f : Hom A C) → Split (restIdemIdemGen f)
restIdemSplitGen f = restIdemSplit _ (sym lemi)

sectionTotProp : {i : Idem}(sp : Split i) → rest (Split.s sp) ≅ iden {Split.B sp}
sectionTotProp {_} sp = lemiii (sectionIsMono sp)

HMap1 : ∀{A C}(f : Hom A C) → Span A C
HMap1 f = 
  let open Split (restIdemSplitGen f)

      sTotProp : rest s ≅ iden {B}
      sTotProp = sectionTotProp (restIdemSplitGen f)

      compfsTotProp : rest (comp f s) ≅ iden
      compfsTotProp =
        proof
        rest (comp f s)
        ≅⟨ lemiv ⟩
        rest (comp (rest f) s)
        ≅⟨ cong (λ y → rest (comp y s)) (sym splitLaw1) ⟩
        rest (comp (comp s r) s)
        ≅⟨ cong rest ass ⟩
        rest (comp s (comp r s))
        ≅⟨ cong (rest ∘ comp s) splitLaw2 ⟩
        rest (comp s iden)
        ≅⟨ cong rest idr ⟩
        rest s
        ≅⟨ sTotProp ⟩
        iden
        ∎ 
   in span B (tot s sTotProp) (tot (comp f s) compfsTotProp) (sridem (rest f) (sym lemi) r splitLaw1 splitLaw2)


fidSpan : ∀{A} → HMap1 iden ~Span~ idSpan {A}
fidSpan = 
  let open Split (restIdemSplitGen iden)

      sTotProp : rest s ≅ iden
      sTotProp = sectionTotProp (restIdemSplitGen iden)

      p : comp s r ≅ iden
      p = 
        proof
        comp s r
        ≅⟨ splitLaw1 ⟩
        rest iden
        ≅⟨ lemiii idMono ⟩
        iden
        ∎

      rTotProp : rest r ≅ iden
      rTotProp = lemiii (isoIsMono cat (iso s splitLaw2 p))
  in spaneq (tot s sTotProp) (iso (tot r rTotProp) (totEq p) (totEq splitLaw2)) (totEq idl) (totEq refl)


fcompSpan : ∀{A C D}{g : Hom C D}{f : Hom A C} → HMap1 (comp g f) ~Span~ compSpan (HMap1 g) (HMap1 f)
fcompSpan {A}{C}{D}{g = g}{f} =
  let open Split (restIdemSplitGen f)
      open Split (restIdemSplitGen g) renaming (B to B'; s to s'; r to r'; splitLaw1 to splitLaw1'; splitLaw2 to splitLaw2')
      open Split (restIdemSplitGen (comp g f)) renaming (B to B''; s to s''; r to r''; splitLaw1 to splitLaw1'''; splitLaw2 to splitLaw2''')

      sTotProp : rest s ≅ iden {B}
      sTotProp = sectionTotProp (restIdemSplitGen f)

      s'TotProp : rest s' ≅ iden
      s'TotProp = sectionTotProp (restIdemSplitGen g)

      compfsTotProp : rest (comp f s) ≅ iden
      compfsTotProp =
        proof
        rest (comp f s)
        ≅⟨ lemiv ⟩
        rest (comp (rest f) s)
        ≅⟨ cong (λ y → rest (comp y s)) (sym splitLaw1) ⟩
        rest (comp (comp s r) s)
        ≅⟨ cong rest ass ⟩
        rest (comp s (comp r s))
        ≅⟨ cong (rest ∘ comp s) splitLaw2 ⟩
        rest (comp s iden)
        ≅⟨ cong rest idr ⟩
        rest s
        ≅⟨ sTotProp ⟩
        iden
        ∎ 

      span _ _ hf _ = HMap1 f
      span _ _ _ mg∈ = HMap1 g

      p , sr = pul∈sysSectionsOfRestIdem hf mg∈

-- (tot (comp f s) compfsTotProp) 
--                                          (sridem {s = tot s' s'TotProp} (rest g) (sym lemi) r' splitLaw1' splitLaw2')

      open Pullback Total p
      open Square Total sq
      tot m _ = h
      tot n _ = k
      sridem _ _ r''' _ _ = sr

      open Split (restIdemSplit (idem B (rest (comp (rest g) (comp f s))) lemii) (sym lemi))
                 renaming (splitLaw1 to splitLaw1''; splitLaw2 to splitLaw2'')
                 hiding (s; r)

      splitLaw1'''' : comp (comp s m) (comp r''' r) ≅ rest (comp g f)
      splitLaw1'''' = 
        proof
        comp (comp s m) (comp r''' r)
        ≅⟨ ass ⟩
        comp s (comp m (comp r''' r))
        ≅⟨ cong (comp s) (sym ass) ⟩
        comp s (comp (comp m r''') r)
        ≅⟨ cong (λ y → comp s (comp y r)) splitLaw1'' ⟩
        comp s (comp (rest (comp (rest g) (comp f s))) r)
        ≅⟨ cong (λ y → comp s (comp y r)) (sym lemiv) ⟩
        comp s (comp (rest (comp g (comp f s))) r)
        ≅⟨ cong (λ y → comp s (comp (rest y) r)) (sym ass) ⟩
        comp s (comp (rest (comp (comp g f) s)) r)
        ≅⟨ sym ass ⟩
        comp (comp s (rest (comp (comp g f) s))) r
        ≅⟨ cong (λ y → comp y r) (sym R4) ⟩
        comp (comp (rest (comp g f)) s) r
        ≅⟨ ass ⟩
        comp (rest (comp g f)) (comp s r)
        ≅⟨ cong (comp (rest (comp g f))) splitLaw1 ⟩
        comp (rest (comp g f)) (rest f)
        ≅⟨ R3 ⟩
        rest (comp (comp g f) (rest f))
        ≅⟨ cong rest ass ⟩
        rest (comp g (comp f (rest f)))
        ≅⟨ cong (rest ∘ comp g) R1 ⟩
        rest (comp g f)
        ∎

      splitLaw2'''' : comp (comp r''' r) (comp s m) ≅ iden {W}
      splitLaw2'''' = 
        proof 
        comp (comp r''' r) (comp s m)
        ≅⟨ ass ⟩
        comp r''' (comp r (comp s m))
        ≅⟨ cong (comp r''') (sym ass) ⟩
        comp r''' (comp (comp r s) m)
        ≅⟨ cong (λ y → comp r''' (comp y m)) splitLaw2 ⟩
        comp r''' (comp iden m)
        ≅⟨ cong (comp r''') idl ⟩
        comp r''' m
        ≅⟨ splitLaw2'' ⟩
        iden
        ∎

      u : Hom B'' W
      u = splitMap (restIdemSplitGen (comp g f)) (split W (comp s m) (comp r''' r) splitLaw1'''' splitLaw2'''')

      uIsIso : Iso cat u
      uIsIso = splitsAreIso (restIdemSplitGen (comp g f)) (split W (comp s m) (comp r''' r) splitLaw1'''' splitLaw2'''')

      uTotProp : rest u ≅ iden {B''}
      uTotProp = lemiii (isoIsMono cat uIsIso)

      rightTr : comp (comp s m) u ≅ s''
      rightTr = splitsAreIsoRightTr (restIdemSplitGen (comp g f)) (split W (comp s m) (comp r''' r) splitLaw1'''' splitLaw2'''')

      leftTr' : comp (comp g s') n ≅ comp (comp g f) (comp s m)
      leftTr' = 
        proof
        comp (comp g s') n
        ≅⟨ refl ⟩
        comp (comp g s') (comp r' (comp (comp f s) m))
        ≅⟨ ass ⟩
        comp g (comp s' (comp r' (comp (comp f s) m)))
        ≅⟨ cong (comp g) (sym ass) ⟩
        comp g (comp (comp s' r') (comp (comp f s) m))
        ≅⟨ cong (λ y → comp g (comp y (comp (comp f s) m))) splitLaw1' ⟩
        comp g (comp (rest g) (comp (comp f s) m))
        ≅⟨ sym ass ⟩
        comp (comp g (rest g)) (comp (comp f s) m)
        ≅⟨ cong (λ y → comp y (comp (comp f s) m)) R1 ⟩
        comp g (comp (comp f s) m)
        ≅⟨ cong (comp g) ass ⟩
        comp g (comp f (comp s m))
        ≅⟨ sym ass ⟩
        comp (comp g f) (comp s m)
        ∎

      leftTr : comp (comp (comp g s') (comp r' (comp (comp f s) m))) u ≅ comp (comp g f) s''
      leftTr =
        proof
        comp (comp (comp g s') (comp r' (comp (comp f s) m))) u
        ≅⟨ cong (λ y → comp y u) leftTr' ⟩
        comp (comp (comp g f) (comp s m)) u
        ≅⟨ ass ⟩
        comp (comp g f) (comp (comp s m) u)
        ≅⟨ cong (comp (comp g f)) rightTr ⟩
        comp (comp g f) s''
        ∎
  in spaneq (tot u uTotProp) (isoTot uIsIso) (totEq rightTr) (totEq leftTr)

fcomp : ∀{A C D}{g : Hom C D}{f : Hom A C} → abs (HMap1 (comp g f)) ≅ qcompSpan (abs (HMap1 g)) (abs (HMap1 f))
fcomp {g = g}{f} = 
  proof
  abs (HMap1 (comp g f)) 
  ≅⟨ sound {mf = HMap1 (comp g f)} fcompSpan ⟩
  abs (compSpan (HMap1 g) (HMap1 f))
  ≅⟨ sym (qcompSpanQbeta {ng = HMap1 g}{HMap1 f}) ⟩
  qcompSpan (abs (HMap1 g)) (abs (HMap1 f))
  ∎

Funct : Fun cat Par
Funct = record { 
  OMap = λ A → A; 
  HMap = abs ∘ HMap1;
  fid = sound fidSpan;
  fcomp = fcomp}

frestSpan : ∀{A C}{f : Hom A C} → restSpan (HMap1 f) ~Span~ HMap1 (rest f)
frestSpan {A}{C}{f} = 
  let open Split (restIdemSplitGen f)
      open Split (restIdemSplitGen (rest f)) renaming (B to B'; s to s')
                 hiding (r; splitLaw1; splitLaw2)

      eq : restIdemIdemGen f ≅ restIdemIdemGen (rest f)
      eq = idemEq refl (sym lemi)

      u : Hom B B'
      u = splitMap≅ eq (restIdemSplitGen f) (restIdemSplitGen (rest f))

      uIsIso : Iso cat u
      uIsIso = splitsAreIso≅ eq (restIdemSplitGen f) (restIdemSplitGen (rest f))

      uTotProp : rest u ≅ iden 
      uTotProp = lemiii (isoIsMono cat uIsIso)

      rightTr : comp s' u ≅ s
      rightTr = splitsAreIsoRightTr≅ eq (restIdemSplitGen f) (restIdemSplitGen (rest f))

      leftTr : comp (comp (rest f) s') u ≅ s
      leftTr = 
        proof
        comp (comp (rest f) s') u
        ≅⟨ ass ⟩
        comp (rest f) (comp s' u)
        ≅⟨ cong (comp (rest f)) rightTr ⟩
        comp (rest f) s
        ≅⟨ cong (λ y → comp y s) (sym splitLaw1) ⟩
        comp (comp s r) s
        ≅⟨ ass ⟩
        comp s (comp r s)
        ≅⟨ cong (comp s) splitLaw2 ⟩
        comp s iden
        ≅⟨ idr ⟩
        s
        ∎
  in spaneq (tot u uTotProp) (isoTot uIsIso) (totEq rightTr) (totEq leftTr)

frest :  ∀{A C}{f : Hom A C} → qrestSpan (abs (HMap1 f)) ≅ abs (HMap1 (rest f))
frest {f = f} = 
  proof
  qrestSpan (abs (HMap1 f))
  ≅⟨ qrestSpanQbeta {mf = HMap1 f} ⟩
  abs (restSpan (HMap1 f))
  ≅⟨ sound {mf = restSpan (HMap1 f)} frestSpan ⟩
  abs (HMap1 (rest f))
  ∎

RFunct : RestFun rcat RestPar
RFunct = record { fun = Funct; frest = frest }

HMap2 : ∀{A C} → Span A C → Hom A C
HMap2 (span _ _ (tot g _) (sridem _ _ r _ _)) = comp g r

compatHMap2 : ∀{A B}{sp sp' : Span A B} → sp ~Span~ sp' → HMap2 sp ≅ HMap2 sp'
compatHMap2 {sp = span _ mt ft m∈}{span _ nt gt n∈} p = 
  let open _~Span~_ p
      open Iso Total sIso
      open Tot s renaming (hom to i; totProp to iTotProp) 
      open Tot inv renaming (hom to j; totProp to jTotProp) 
      open Tot gt renaming (hom to g; totProp to gTotProp) 
      open Tot ft renaming (hom to f; totProp to fTotProp) 
      open Tot nt renaming (hom to n; totProp to nTotProp) 
      open Tot mt renaming (hom to m; totProp to mTotProp) 
      open SectionOfRestIdem m∈
      open SectionOfRestIdem n∈ renaming (e to e'; r to r'; splitLaw1 to splitLaw1'; splitLaw2 to splitLaw2')
  in
    proof
    comp f r
    ≅⟨ cong (λ y → comp y r) (sym (totEqHom rightTr)) ⟩
    comp (comp g i) r
    ≅⟨ ass ⟩
    comp g (comp i r)
    ≅⟨ cong (λ y → comp g (comp y r)) (sym idl) ⟩
    comp g (comp (comp iden i) r)
    ≅⟨ cong (λ y → comp g (comp (comp y i) r)) (sym splitLaw2') ⟩
    comp g (comp (comp (comp r' n) i) r)
    ≅⟨ cong (λ y → comp g (comp y r)) ass ⟩
    comp g (comp (comp r' (comp n i)) r)
    ≅⟨ cong (λ y → comp g (comp (comp r' y) r)) (totEqHom leftTr) ⟩
    comp g (comp (comp r' m) r)
    ≅⟨ cong (comp g) ass ⟩
    comp g (comp r' (comp m r))
    ≅⟨ cong ((comp g) ∘ (comp r')) splitLaw1 ⟩
    comp g (comp r' e)
    ≅⟨ cong ((comp g) ∘ (comp r')) (restRetractionProp m∈) ⟩ 
    comp g (comp r' (rest r))
    ≅⟨ cong (λ y → comp g (comp y (rest r))) (sym R1) ⟩
    comp g (comp (comp r' (rest r')) (rest r))
    ≅⟨ cong (comp g) ass ⟩
    comp g (comp r' (comp (rest r') (rest r)))
    ≅⟨ cong ((comp g) ∘ (comp r')) R2 ⟩
    comp g (comp r' (comp (rest r) (rest r')))
    ≅⟨ cong ((comp g) ∘ (comp r')) R3 ⟩
    comp g (comp r' (rest (comp r (rest r'))))
    ≅⟨ cong ((comp g) ∘ (comp r') ∘ rest) (sym idl) ⟩
    comp g (comp r' (rest (comp iden (comp r (rest r')))))
    ≅⟨ cong (λ y → comp g (comp r' (rest (comp y (comp r (rest r')))))) (sym iTotProp) ⟩
    comp g (comp r' (rest (comp (rest i) (comp r (rest r')))))
    ≅⟨ cong ((comp g) ∘ (comp r')) (sym lemiv) ⟩ 
    comp g (comp r' (rest (comp i (comp r (rest r')))))
    ≅⟨ cong ((comp g) ∘ (comp r') ∘ rest ∘ (comp i) ∘ (comp r)) (sym (restRetractionProp n∈)) ⟩
    comp g (comp r' (rest (comp i (comp r e'))))
    ≅⟨ cong ((comp g) ∘ (comp r') ∘ rest ∘ (comp i) ∘ (comp r)) (sym splitLaw1') ⟩ 
    comp g (comp r' (rest (comp i (comp r (comp n r')))))
    ≅⟨ cong ((comp g) ∘ (comp r') ∘ rest ∘ comp i) (sym ass) ⟩
    comp g (comp r' (rest (comp i (comp (comp r n) r'))))
    ≅⟨ cong (λ y → comp g (comp r' (rest (comp i (comp (comp r y) r'))))) (sym idr) ⟩
    comp g (comp r' (rest (comp i (comp (comp r (comp n iden)) r'))))
    ≅⟨ cong (λ y → comp g (comp r' (rest (comp i (comp (comp r (comp n y)) r'))))) (totEqHom (sym rinv)) ⟩
    comp g (comp r' (rest (comp i (comp (comp r (comp n (comp i j))) r'))))
    ≅⟨ cong (λ y → comp g (comp r' (rest (comp i (comp (comp r y) r'))))) (sym ass) ⟩
    comp g (comp r' (rest (comp i (comp (comp r (comp (comp n i) j)) r'))))
    ≅⟨ cong (λ y → comp g (comp r' (rest (comp i (comp (comp r (comp y j)) r'))))) (totEqHom leftTr) ⟩
    comp g (comp r' (rest (comp i (comp (comp r (comp m j)) r'))))
    ≅⟨ cong (λ y → comp g (comp r' (rest (comp i (comp y r'))))) (sym ass) ⟩
    comp g (comp r' (rest (comp i (comp (comp (comp r m) j) r'))))
    ≅⟨ cong (λ y → comp g (comp r' (rest (comp i (comp (comp y j) r'))))) splitLaw2 ⟩
    comp g (comp r' (rest (comp i (comp (comp iden j) r'))))
    ≅⟨ cong (λ y → comp g (comp r' (rest (comp i (comp y r'))))) idl ⟩
    comp g (comp r' (rest (comp i (comp j r'))))
    ≅⟨ cong ((comp g) ∘ (comp r') ∘ rest) (sym ass) ⟩
    comp g (comp r' (rest (comp (comp i j) r')))
    ≅⟨ cong (λ y → comp g (comp r' (rest (comp y r')))) (totEqHom rinv) ⟩ 
    comp g (comp r' (rest (comp iden r')))
    ≅⟨ cong ((comp g) ∘ (comp r') ∘ rest) idl ⟩
    comp g (comp r' (rest r'))
    ≅⟨ cong (comp g) R1 ⟩
    comp g r'
    ∎

qHMap2 : ∀{A C} → QSpan A C → Hom A C
qHMap2 {A}{C} = lift {A}{C} HMap2 compatHMap2

qHMap2Qbeta : ∀{A C}{mf : Span A C} → qHMap2 (abs mf) ≅ HMap2 mf
qHMap2Qbeta {A}{C}{mf} = qbeta {A}{C} (λ _ → Hom A C) HMap2 compatHMap2 mf

fid2 : ∀{A} → qHMap2 (abs (idSpan {A})) ≅ iden
fid2 = 
  proof
  qHMap2 (abs idSpan)
  ≅⟨ qHMap2Qbeta {mf = idSpan} ⟩ 
  HMap2 idSpan
  ≅⟨ idl ⟩
  iden
  ∎

fcomp2Span : ∀{A B C}{ng : Span B C}{mf : Span A B} → HMap2 (compSpan ng mf) ≅ comp (HMap2 ng) (HMap2 mf)
fcomp2Span {ng = ng}{mf} =
  let span _ _ (tot f p) m∈ = mf
      span _ (tot n _) (tot g _) m∈' = ng
      sridem _ _ rf _ _ = m∈
      open SectionOfRestIdem m∈' renaming (e to e'; restIdem to e'RestIdem; r to r'; splitLaw1 to splitLaw1'; splitLaw2 to splitLaw2')        
      pullback (square _ (tot m' _) _ _) _ , z = pul∈sysSectionsOfRestIdem (tot f p) m∈'
      open SectionOfRestIdem z renaming (r to r''; splitLaw1 to splitLaw1'')
  in 
    proof 
    comp (comp g (comp r' (comp f m'))) (comp r'' rf) 
    ≅⟨ sym ass ⟩
    comp (comp (comp g (comp r' (comp f m'))) r'') rf
    ≅⟨ cong (λ y → comp y rf) ass ⟩ 
    comp (comp g (comp (comp r' (comp f m')) r'')) rf
    ≅⟨ cong (λ y → comp (comp g y) rf) ass ⟩ 
    comp (comp g (comp r' (comp (comp f m') r''))) rf
    ≅⟨ cong (λ y → comp (comp g (comp r' y)) rf) ass ⟩ 
    comp (comp g (comp r' (comp f (comp m' r'')))) rf
    ≅⟨ cong (λ y → comp (comp g (comp r' (comp f y))) rf) splitLaw1'' ⟩
    comp (comp g (comp r' (comp f (rest (comp e' f))))) rf
    ≅⟨ cong (λ y → comp (comp g (comp r' y)) rf) (sym R4) ⟩
    comp (comp g (comp r' (comp (rest e') f))) rf
    ≅⟨ cong (λ y → comp (comp g (comp r' (comp y f))) rf) (sym e'RestIdem) ⟩
    comp (comp g (comp r' (comp e' f))) rf
    ≅⟨ cong (λ y → comp (comp g (comp r' (comp y f))) rf) (sym splitLaw1') ⟩
    comp (comp g (comp r' (comp (comp n r') f))) rf
    ≅⟨ cong (λ y → comp (comp g (comp r' y)) rf) ass ⟩
    comp (comp g (comp r' (comp n (comp r' f)))) rf
    ≅⟨ cong (λ y → comp (comp g y) rf) (sym ass) ⟩
    comp (comp g (comp (comp r' n) (comp r' f))) rf
    ≅⟨ cong (λ y → comp (comp g (comp y (comp r' f))) rf) splitLaw2' ⟩
    comp (comp g (comp iden (comp r' f))) rf
    ≅⟨ cong (λ y → comp (comp g y) rf) idl ⟩
    comp (comp g (comp r' f)) rf
    ≅⟨ cong (λ y → comp y rf) (sym ass) ⟩
    comp (comp (comp g r') f) rf
    ≅⟨ ass ⟩
    comp (comp g r') (comp f rf) 
    ∎

fcomp2 : ∀{A B C}{ng : QSpan B C}{mf : QSpan A B} → qHMap2 (qcompSpan ng mf) ≅ comp (qHMap2 ng) (qHMap2 mf)
fcomp2 {A}{B}{C}{ng}{mf} = 
  qelim₂ (λ ng mf → qHMap2 (qcompSpan ng mf) ≅ comp (qHMap2 ng) (qHMap2 mf)) 
         (λ ng mf →
           proof
           qHMap2 (qcompSpan (abs ng) (abs mf)) 
           ≅⟨ cong qHMap2 qcompSpanQbeta ⟩
           qHMap2 (abs (compSpan ng mf))
           ≅⟨ qHMap2Qbeta ⟩
           HMap2 (compSpan ng mf)
           ≅⟨ fcomp2Span {ng = ng}{mf} ⟩
           comp (HMap2 ng) (HMap2 mf)
           ≅⟨ cong₂ comp (sym qHMap2Qbeta) (sym qHMap2Qbeta) ⟩
           comp (qHMap2 (abs ng)) (qHMap2 (abs mf))
           ∎)
         (λ p q → hirR (cong₂ (λ (x : QSpan B C) (y : QSpan A B) → comp (qHMap2 x) (qHMap2 y)) (sound p) (sound q)))
         ng mf

Funct2 : Fun Par cat
Funct2 = record {
  OMap = λ A → A; 
  HMap = qHMap2;
  fid = fid2;
  fcomp = fcomp2 }

frestSpan2 : ∀{A B}{mf : Span A B} → rest (HMap2 mf) ≅ HMap2 (restSpan mf)
frestSpan2 {mf = span _ (tot m _) fhom m∈} = 
  let open Tot fhom renaming (hom to f; totProp to fTotProp)
      open SectionOfRestIdem m∈
  in 
    proof
    rest (comp f r)
    ≅⟨ lemiv ⟩
    rest (comp (rest f) r)
    ≅⟨ cong (λ y → rest (comp y r)) fTotProp ⟩
    rest (comp iden r)
    ≅⟨ cong rest idl ⟩
    rest r
    ≅⟨ sym (restRetractionProp m∈) ⟩
    e
    ≅⟨ sym splitLaw1 ⟩
    comp m r
    ∎

frest2 : ∀{A B}{mf : QSpan A B} → rest (qHMap2 mf) ≅ qHMap2 (qrestSpan mf)
frest2 {mf = mf} = 
  qelim (λ mf → rest (qHMap2 mf) ≅ qHMap2 (qrestSpan mf)) 
        (λ mf → 
          proof
          rest (qHMap2 (abs mf)) 
          ≅⟨ cong rest qHMap2Qbeta  ⟩
          rest (HMap2 mf) 
          ≅⟨ frestSpan2 {mf = mf} ⟩
          HMap2 (restSpan mf) 
          ≅⟨ sym qHMap2Qbeta ⟩
          qHMap2 (abs (restSpan mf))
          ≅⟨ cong qHMap2 (sym qrestSpanQbeta) ⟩
          qHMap2 (qrestSpan (abs mf))
          ∎)
        (hirL ∘ (cong (rest ∘ qHMap2) ∘ sound)) 
        mf

RFunct2 : RestFun RestPar rcat
RFunct2 = record { fun = Funct2 ; frest = frest2 }

open Fun

-- Iso proof

HIso1Span : ∀{A C}(mf : Span A C) → HMap1 (HMap2 mf) ~Span~ mf
HIso1Span mf = 
  let span A' (tot m _) fhom m∈ = mf 
      span A'' (tot n _) _ n∈ = HMap1 (HMap2 mf)
      open Tot fhom renaming (hom to f; totProp to fTotProp)
      open SectionOfRestIdem m∈
      open SectionOfRestIdem n∈ renaming (e to e'; r to r'; splitLaw1 to splitLaw1'; splitLaw2 to splitLaw2')

      splitLaw1'' : comp m r ≅ rest r
      splitLaw1'' = proof comp m r ≅⟨ splitLaw1 ⟩ e ≅⟨ restRetractionProp m∈ ⟩ rest r ∎

      splitLaw1''' : comp n r' ≅ rest r
      splitLaw1''' = 
        proof
        comp n r'
        ≅⟨ splitLaw1' ⟩
        rest (comp f r)
        ≅⟨ lemiv ⟩
        rest (comp (rest f) r)
        ≅⟨ cong (λ y → rest (comp y r)) fTotProp ⟩
        rest (comp iden r)
        ≅⟨ cong rest idl ⟩
        rest r
        ∎

      sp : Split (restIdemIdemGen r)
      sp = split _ m r splitLaw1'' splitLaw2 

      sp' : Split (restIdemIdemGen r)
      sp' = split _ n r' splitLaw1''' splitLaw2'

      u : Hom A' A''
      u = splitMap sp sp' 

      uTotProp : rest u ≅ iden
      uTotProp = lemiii (isoIsMono cat (splitsAreIso sp sp'))

      rightTr : comp n u ≅ m
      rightTr = splitsAreIsoRightTr sp sp'

      leftTr : comp (comp (comp f r) n) u ≅ f
      leftTr = 
        proof
        comp (comp (comp f r) n) u 
        ≅⟨ ass ⟩
        comp (comp f r) (comp n u) 
        ≅⟨ cong (comp (comp f r)) rightTr ⟩
        comp (comp f r) m 
        ≅⟨ ass ⟩
        comp f (comp r m) 
        ≅⟨ cong (comp f) splitLaw2 ⟩
        comp f iden
        ≅⟨ idr ⟩
        f
        ∎
  in ~sym (spaneq (tot u uTotProp) (isoTot (splitsAreIso sp sp')) (totEq rightTr) (totEq leftTr))

HIso1 : ∀{A C}(mf : QSpan A C) → abs (HMap1 (qHMap2 mf)) ≅ mf
HIso1 = 
  qelim (λ mf → abs (HMap1 (qHMap2 mf)) ≅ mf) 
        (λ mf → 
           proof
           abs (HMap1 (qHMap2 (abs mf)))
           ≅⟨ cong (abs ∘ HMap1) qHMap2Qbeta ⟩
           abs (HMap1 (HMap2 mf))
           ≅⟨ sound (HIso1Span mf) ⟩
           abs mf
           ∎)
        (hirR ∘ sound)


HIso2 : ∀{A C}(f : Hom A C) → qHMap2 (abs (HMap1 f)) ≅ f
HIso2 f = 
  let open Split (restIdemSplitGen f)
  in 
    proof
    qHMap2 (abs (HMap1 f))
    ≅⟨ qHMap2Qbeta ⟩
    comp (comp f s) r
    ≅⟨ ass ⟩
    comp f (comp s r)
    ≅⟨ cong (comp f) splitLaw1 ⟩
    comp f (rest f)
    ≅⟨ R1 ⟩
    f
    ∎

{-
{-






  IsoCompl : Iso CCat Funct
  IsoCompl = Funct2 ,, 
             Fun≅ refl HIso1 ,, 
             Fun≅ refl HIso2

  RIsoCompl : Iso RCCat RFunct
  RIsoCompl = RFunct2 ,, 
              RFun≅ (Fun≅ refl HIso1) ,, 
              RFun≅ (Fun≅ refl HIso2)





-}
-}



