open import Categories

module Categories.Idems (X : Cat) where
  open import Utilities

  open Cat X

  record Idem : Set where
    field E : Obj
          e : Hom E E
          .law : comp e e ≅ e

  .idem≅ : ∀{ide ide' : Idem} → 
                    let open Idem ide
                        open Idem ide' renaming (E to E'; e to e')
                    in E ≅ E' → e ≅ e' → ide ≅ ide'
  idem≅ {ide} {ide'} p q = cong₃ 
    {A = Obj}
    {B = λ E → Hom E E}
    {C = λ E e → comp e e ≅ e}
    {D = λ _ _ _ → Idem}
    p 
    q 
    {c = Idem.law ide}
    (fixtypes'' q)
    (λ x y z → record { E = x; e = y; law = z })

  record Split (ide : Idem) : Set where
    open Idem ide
    field B : Obj 
          s : Hom B E
          r : Hom E B
          .law1 : comp s r ≅ e
          .law2 : comp r s ≅ iden {B}

  open import Categories.Epis X
  open import Categories.Monos X

  .repi : ∀{e : Idem}{sp : Split e} → 
         let open Split sp
         in
         Epi r
  repi {_}{sp}{_}{g}{h} p = 
    let open Split sp
    in
    proof 
    g 
    ≅⟨ sym idr ⟩ 
    comp g iden 
    ≅⟨ cong (comp g) (sym law2) ⟩ 
    comp g (comp r s) 
    ≅⟨ sym ass ⟩ 
    comp (comp g r) s 
    ≅⟨ cong (λ y → comp y s) p ⟩ 
    comp (comp h r) s 
    ≅⟨ ass ⟩ 
    comp h (comp r s) 
    ≅⟨ cong (comp h) law2 ⟩ 
    comp h iden 
    ≅⟨ idr ⟩ 
    h 
    ∎

  import Categories.Isos

  lemmamap : ∀(e : Idem)(sp sp' : Split e) → 
             let open Categories.Isos X
                 open Split sp
                 open Split sp' renaming (B to B')
             in
             Σ (Hom B B') λ α → Iso α
  lemmamap ide sp sp' =  
    let open Categories.Isos X
        open Idem ide
        open Split sp
        open Split sp' renaming (B to B'; 
                                 s to s'; 
                                 r to r';
                                 law1 to law1';
                                 law2 to law2')
    in comp r' s 
       , 
       (comp r s' 
        ,, 
        (proof 
         comp (comp r' s) (comp r s') 
         ≅⟨ ass ⟩ 
         comp r' (comp s (comp r s'))
         ≅⟨ cong (comp r') (sym ass) ⟩ 
         comp r' (comp (comp s r) s')
         ≅⟨ cong (λ f → comp r' (comp f s')) law1 ⟩ 
         comp r' (comp e s')
         ≅⟨ cong (λ f → comp r' (comp f s')) (sym law1') ⟩ 
         comp r' (comp (comp s' r') s')
         ≅⟨ cong (comp r') ass ⟩
         comp r' (comp s' (comp r' s'))
         ≅⟨ cong (comp r' ∘ comp s') law2' ⟩
         comp r' (comp s' iden)
         ≅⟨ sym ass ⟩
         comp (comp r' s') iden
         ≅⟨ idr ⟩
         comp r' s'
         ≅⟨ law2' ⟩
         iden 
         ∎) 
        ,,
        (proof 
         comp (comp r s') (comp r' s) 
         ≅⟨ ass ⟩
         comp r (comp s' (comp r' s))
         ≅⟨ cong (comp r) (sym ass) ⟩ 
         comp r (comp (comp s' r') s)
         ≅⟨ cong (λ f → comp r (comp f s)) law1' ⟩ 
         comp r (comp e s)
         ≅⟨ cong (λ f → comp r (comp f s)) (sym law1) ⟩ 
         comp r (comp (comp s r) s)
         ≅⟨ cong (comp r) ass ⟩
         comp r (comp s (comp r s))
         ≅⟨ cong (comp r ∘ comp s) law2 ⟩
         comp r (comp s iden)
         ≅⟨ sym ass ⟩
         comp (comp r s) iden
         ≅⟨ idr ⟩
         comp r s
         ≅⟨ law2 ⟩
         iden 
         ∎))

  .lemmalaw1 : ∀(e : Idem)(sp sp' : Split e) → 
              let open Categories.Isos X
                  open Split sp
                  open Split sp' renaming (r to r')
                  α = proj₁ (lemmamap e sp sp')
              in comp α r ≅ r'
  lemmalaw1 ide sp sp' =
    let open Categories.Isos X
        open Idem ide
        open Split sp
        open Split sp' renaming (B to B'; 
                                 s to s'; 
                                 r to r';
                                 law1 to law1';
                                 law2 to law2')
    in 
      proof 
      comp (comp r' s) r 
      ≅⟨ ass ⟩ 
      comp r' (comp s r)
      ≅⟨ cong (comp r') law1 ⟩ 
      comp r' e
      ≅⟨ cong (comp r') (sym law1') ⟩ 
      comp r' (comp s' r')
      ≅⟨ sym ass ⟩ 
      comp (comp r' s') r'
      ≅⟨ cong (λ f → comp f r') law2' ⟩ 
      comp iden r'
      ≅⟨ idl ⟩ 
      r'
      ∎

  .lemmalaw2 : ∀(e : Idem)(sp sp' : Split e) → 
              let open Categories.Isos X
                  open Split sp
                  open Split sp' renaming (s to s')
                  α = proj₁ (lemmamap e sp sp')
              in comp s' α ≅ s
  lemmalaw2 ide sp sp' =
    let open Categories.Isos X
        open Idem ide
        open Split sp
        open Split sp' renaming (B to B'; 
                                 s to s'; 
                                 r to r';
                                 law1 to law1';
                                 law2 to law2')
    in 
      proof 
      comp s' (comp r' s) 
      ≅⟨ sym ass ⟩ 
      comp (comp s' r') s
      ≅⟨ cong (λ f → comp f s) law1' ⟩ 
      comp e s
      ≅⟨ cong (λ f → comp f s) (sym law1) ⟩ 
      comp (comp s r) s
      ≅⟨ ass ⟩ 
      comp s (comp r s)
      ≅⟨ cong (comp s) law2 ⟩ 
      comp s iden
      ≅⟨ idr ⟩ 
      s
      ∎

{-
  lemma : ∀(e : Idem)(sp sp' : Split e) → 
          let open Categories.Isos X
              open Split sp
              open Split sp' renaming (B to B'; s to s'; r to r')
          in
          Σ' (Hom B B') λ α → Iso α × (comp α r ≅ r') × comp s' α ≅ s
  lemma ide sp sp' =  
    let open Categories.Isos X
        open Idem ide
        open Split sp
        open Split sp' renaming (B to B'; 
                                 s to s'; 
                                 r to r';
                                 law1 to law1';
                                 law2 to law2')
    in comp r' s 
       ,, 
       (comp r s' 
        ,, 
        (proof 
         comp (comp r' s) (comp r s') 
         ≅⟨ ass ⟩ 
         comp r' (comp s (comp r s'))
         ≅⟨ cong (comp r') (sym ass) ⟩ 
         comp r' (comp (comp s r) s')
         ≅⟨ cong (λ f → comp r' (comp f s')) law1 ⟩ 
         comp r' (comp e s')
         ≅⟨ cong (λ f → comp r' (comp f s')) (sym law1') ⟩ 
         comp r' (comp (comp s' r') s')
         ≅⟨ cong (comp r') ass ⟩
         comp r' (comp s' (comp r' s'))
         ≅⟨ cong (comp r' ∘ comp s') law2' ⟩
         comp r' (comp s' iden)
         ≅⟨ sym ass ⟩
         comp (comp r' s') iden
         ≅⟨ idr ⟩
         comp r' s'
         ≅⟨ law2' ⟩
         iden 
         ∎) 
        ,,
        (proof 
         comp (comp r s') (comp r' s) 
         ≅⟨ ass ⟩
         comp r (comp s' (comp r' s))
         ≅⟨ cong (comp r) (sym ass) ⟩ 
         comp r (comp (comp s' r') s)
         ≅⟨ cong (λ f → comp r (comp f s)) law1' ⟩ 
         comp r (comp e s)
         ≅⟨ cong (λ f → comp r (comp f s)) (sym law1) ⟩ 
         comp r (comp (comp s r) s)
         ≅⟨ cong (comp r) ass ⟩
         comp r (comp s (comp r s))
         ≅⟨ cong (comp r ∘ comp s) law2 ⟩
         comp r (comp s iden)
         ≅⟨ sym ass ⟩
         comp (comp r s) iden
         ≅⟨ idr ⟩
         comp r s
         ≅⟨ law2 ⟩
         iden 
         ∎))
       , 
       ((proof 
        comp (comp r' s) r 
        ≅⟨ ass ⟩ 
        comp r' (comp s r)
        ≅⟨ cong (comp r') law1 ⟩ 
        comp r' e
        ≅⟨ cong (comp r') (sym law1') ⟩ 
        comp r' (comp s' r')
        ≅⟨ sym ass ⟩ 
        comp (comp r' s') r'
        ≅⟨ cong (λ f → comp f r') law2' ⟩ 
        comp iden r'
        ≅⟨ idl ⟩ 
        r'
        ∎) 
       , 
       (proof 
        comp s' (comp r' s) 
        ≅⟨ sym ass ⟩ 
        comp (comp s' r') s
        ≅⟨ cong (λ f → comp f s) law1' ⟩ 
        comp e s
        ≅⟨ cong (λ f → comp f s) (sym law1) ⟩ 
        comp (comp s r) s
        ≅⟨ ass ⟩ 
        comp s (comp r s)
        ≅⟨ cong (comp s) law2 ⟩ 
        comp s iden
        ≅⟨ idr ⟩ 
        s
        ∎))
-}

  lemmamap' : ∀(e e' : Idem) → e ≅ e' → (sp : Split e)(sp' : Split e') → 
             let open Categories.Isos X
                 open Split sp
                 open Split sp' renaming (B to B')
             in
             Σ (Hom B B') λ α → Iso α
  lemmamap' e .e refl sp sp' = lemmamap e sp sp'

  .lemmalaw1' : ∀(e e' : Idem) → (p : e ≅ e') → (sp : Split e)(sp' : Split e') → 
              let open Categories.Isos X
                  open Split sp
                  open Split sp' renaming (r to r')
                  α = proj₁ (lemmamap' e e' p sp sp')
              in comp α r ≅ r'
  lemmalaw1' e .e refl sp sp' = lemmalaw1 e sp sp'

  .lemmalaw2' : ∀(e e' : Idem) → (p : e ≅ e') → (sp : Split e)(sp' : Split e') → 
              let open Categories.Isos X
                  open Split sp
                  open Split sp' renaming (s to s')
                  α = proj₁ (lemmamap' e e' p sp sp')
              in comp s' α ≅ s
  lemmalaw2' e .e refl sp sp' = lemmalaw2 e sp sp'

{-
  .lemma' : ∀(e e' : Idem) → e ≅ e' → (sp : Split e)(sp' : Split e') → 
            let open Categories.Isos X
                open Split sp
                open Split sp' renaming (B to B'; s to s'; r to r')
            in Σ (Hom B B') λ α → Iso α × (comp α r ≅ r') × comp s' α ≅ s
  lemma' e .e refl sp sp' = lemma e sp sp'
-}
