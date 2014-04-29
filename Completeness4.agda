open import Restriction.SplitRestCats

module Completeness4 (X : SplitRestCat) where
  open import Utilities
  open import Categories
  open import Restriction.Cat
  open import Categories.Functors
  open import Restriction.Functors
  open SplitRestCat X
  open RestCat rcat

  open Cat cat
  open import Restriction.Totals rcat
  open Tot
  open import PartialMaps.Stable 
  open import Categories.Pullbacks
  open Lemmata

  open import PartialMaps.MonicClasses X

  open import PartialMaps.Cat Total M
  open import Soundness Total M
  open import Categories.Idems cat
  open import Categories.Sections cat
  open import Categories.Monos cat
  open import Categories.Isos
  open import Completeness X
  open import Completeness2 X
  open import Completeness3 X

  .fcomp2 : ∀{A B C}{q' : QSpan B C}{q : QSpan A B} → qHMap2 (qcomp q' q) ≅ comp (qHMap2 q') (qHMap2 q)
  fcomp2 {A}{B}{C}{q'}{q} = Quotient.lift (quot (Span B C) Span~EqR)
                                          {λ y → qHMap2 (qcomp y q) ≅ comp (qHMap2 y) (qHMap2 q)} 
                                          (λ a → Quotient.lift (quot (Span A B) Span~EqR)
                                                               {λ y → qHMap2 (qcomp (abs a) y) ≅ comp (qHMap2 (abs a)) (qHMap2 y)}
                                                               (λ b → 
                                                                 proof
                                                                 qHMap2 (qcomp (abs a) (abs b))
                                                                 ≅⟨ cong qHMap2 qcompabsabs ⟩
                                                                 qHMap2 (abs (compspan a b))
                                                                 ≅⟨ ax3 HMap2 compatHMap2 (compspan a b) ⟩
                                                                 HMap2 (compspan a b)
                                                                 ≅⟨ fcomp2' {A}{B}{C}{sp' = a}{sp = b} ⟩
                                                                 comp (HMap2 a) (HMap2 b)
                                                                 ≅⟨ cong (comp (HMap2 a)) (sym (ax3 HMap2 compatHMap2 b)) ⟩
                                                                 comp (HMap2 a) (qHMap2 (abs b))
                                                                 ≅⟨ cong (λ y → comp y (qHMap2 (abs b))) (sym (ax3 HMap2 compatHMap2 a)) ⟩ 
                                                                 comp (qHMap2 (abs a)) (qHMap2 (abs b))
                                                                 ∎)
                                                               (λ x → fixtypes' (cong (λ y → qHMap2 (qcomp (abs a) y)) (ax1 _ _ x)) )
                                                               q)
                                          (λ x → fixtypes' (cong (λ y → qHMap2 (qcomp y q)) (ax1 _ _ x)))
                                          q'

{-
  Funct2 : Fun Par cat
  Funct2 = record {
    OMap = λ A → A; 
    HMap = qHMap2;
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

  RFunct2 : RestFun RestPartials rcat
  RFunct2 = record {
    fun = Funct2;
    frest = λ {A}{B}{f} → Quotient.lift (quot (Span A B) Span~EqR)
                                          {λ y → rest (qHMap2 y) ≅ qHMap2 (qrest y)} 
                                          (λ a → 
                                            proof 
                                            rest (qHMap2 (abs a))
                                            ≅⟨ cong rest (ax3 HMap2 compatHMap2 a) ⟩ 
                                            rest (HMap2 a)
                                            ≅⟨ frest2' {sp = a} ⟩ 
                                            HMap2 (restp a)
                                            ≅⟨ sym (ax3 HMap2 compatHMap2 (restp a)) ⟩ 
                                            qHMap2 (abs (restp a))
                                            ≅⟨ cong qHMap2 (sym qrestabs≅) ⟩ 
                                            qHMap2 (qrest (abs a)) 
                                            ∎) 
                                          (λ x → fixtypes' (cong (rest ∘ qHMap2) (ax1 _ _ x)))
                                          f }

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
                (TotEq {g = nt} (lemmalaw2 (record { E = A; e = rest r; law = lemii rcat}) spl spl'))
                (TotEq {g = gt} equat))

  .HIso1 : ∀{A B}(q : QSpan A B) → abs (HMap1 (qHMap2 q)) ≅ q
  HIso1 {A}{B} q = Quotient.lift (quot (Span A B) Span~EqR)
                                 {λ y → abs (HMap1 (qHMap2 y)) ≅ y}
                                 (λ a → 
                                   proof
                                   abs (HMap1 (qHMap2 (abs a)))
                                   ≅⟨ cong (abs ∘ HMap1) (ax3 HMap2 compatHMap2 a) ⟩
                                   abs (HMap1 (HMap2 a))
                                   ≅⟨ ax1 _ _ (HIso1' a) ⟩
                                   abs a
                                   ∎)
                                 (λ x → fixtypes'' (ax1 _ _ x))
                                 q

  .HIso2' : ∀{A C}(f : Hom A C) → HMap2 (HMap1 f) ≅ f
  HIso2' {A}{C} f = 
    let ide : Idem 
        ide = record { 
          E = A ; 
          e = rest f ; 
          law = lemii rcat }

        .restide : RestIdem rcat ide
        restide = sym (lemi rcat) 

        open Split (rsplit ide restide)
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

  .HIso2 : ∀{A B}(f : Hom A B) → qHMap2 (abs (HMap1 f)) ≅ f
  HIso2 f = 
    proof
    qHMap2 (abs (HMap1 f))
    ≅⟨ ax3 HMap2 compatHMap2 (HMap1 f) ⟩
    HMap2 (HMap1 f)
    ≅⟨ HIso2' f ⟩
    f
    ∎

  IsoCompl : Iso CCat Funct
  IsoCompl = Funct2 ,, 
             Fun≅ refl HIso1 ,, 
             Fun≅ refl HIso2

  RIsoCompl : Iso RCCat RFunct
  RIsoCompl = RFunct2 ,, 
              RFun≅ (Fun≅ refl HIso1) ,, 
              RFun≅ (Fun≅ refl HIso2)
-}