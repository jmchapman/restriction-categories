{-# OPTIONS --type-in-type #-}
open import Categories
open import PartialMaps.Stable
open import Utilities

module PartialMaps.Cat (X : Cat)(M : StableSys X) where

    open Cat X
    open StableSys X M
    open import Categories.Isos X
    open import Categories.Pullbacks X
    open import Categories.Monos X
    open import Categories.Pullbacks.PullbacksLemmas X
    open import Categories.Pullbacks.PastingLemmas X

    record Span (A B : Obj) : Set where
      constructor span
      field A' : Obj
            mhom : Hom A' A
            fhom : Hom A' B
            m∈ : ∈ mhom

    record _~Span~_ {A B}(mf m'f' : Span A B) : Set where
      constructor spaneq 
      field s : Hom (Span.A' mf) (Span.A' m'f')
            siso :   Iso s
            .p  : comp (Span.mhom m'f') s ≅ (Span.mhom mf)
            .q  : comp (Span.fhom m'f') s ≅ (Span.fhom mf)

    ~refl : ∀{A B}{mf : Span A B} → mf ~Span~ mf
    ~refl = spaneq iden idiso idr idr

    ~sym : ∀{A B}{mf m'f' : Span A B} → mf ~Span~ m'f' → m'f' ~Span~ mf
    ~sym {A}{B}{mf}{m'f'} (spaneq s (inv ,, rinv ,, linv) q r) = 
      let open Span mf renaming (mhom to m; fhom to f)
          open Span m'f' renaming (mhom to m'; fhom to f')
      in spaneq 
        inv 
        (s ,, linv ,, rinv) 
        (proof 
         comp m inv 
         ≅⟨ cong (λ x → comp x inv) (sym q) ⟩ 
         comp (comp m' s) inv 
         ≅⟨ ass ⟩ 
         comp m' (comp s inv)
         ≅⟨ cong (comp m') rinv ⟩ 
         comp m' iden
         ≅⟨ idr ⟩ 
         m' ∎) 
        (proof 
         comp f inv 
         ≅⟨ cong (λ x → comp x inv) (sym r) ⟩ 
         comp (comp f' s) inv 
         ≅⟨ ass ⟩ 
         comp f' (comp s inv)
         ≅⟨ cong (comp f') rinv ⟩ 
         comp f' iden
         ≅⟨ idr ⟩ 
         f' ∎) 

    ~trans : ∀{A B}{mf m'f' m''f'' : Span A B} → 
              mf ~Span~ m'f' → m'f' ~Span~ m''f'' → mf ~Span~ m''f''
    ~trans {A}{B}{mf}{m'f'}{m''f''} (spaneq s iso p q) (spaneq s' iso' p' q') =
      let open Span mf renaming (mhom to m; fhom to f)
          open Span m'f' renaming (mhom to m'; fhom to f')
          open Span m''f'' renaming (mhom to m''; fhom to f'')
          open Iso iso renaming (inv to invs; rinv to rinvs; linv to linvs)
          open Iso iso' renaming (inv to invs'; rinv to rinvs'; linv to linvs')
      in spaneq 
        (comp s' s) 
        (comp invs invs' 
         ,, 
         (proof 
          comp (comp s' s) (comp invs invs') 
          ≅⟨ ass ⟩ 
          comp s' (comp s (comp invs invs'))
          ≅⟨ cong (comp s') (sym ass) ⟩ 
          comp s' (comp (comp s invs) invs')
          ≅⟨ cong (λ x → comp s' (comp x invs')) rinvs ⟩ 
          comp s' (comp iden invs')
          ≅⟨ cong (comp s') idl ⟩ 
          comp s' invs'
          ≅⟨ rinvs' ⟩ 
          iden ∎)
         ,, 
         (proof 
          comp (comp invs invs') (comp s' s) 
          ≅⟨ ass ⟩ 
          comp invs (comp invs' (comp s' s))
          ≅⟨ cong (comp invs) (sym ass) ⟩ 
          comp invs (comp (comp invs' s') s)
          ≅⟨ cong (λ x → comp invs (comp x s)) linvs' ⟩ 
          comp invs (comp iden s)
          ≅⟨ cong (comp invs) idl ⟩ 
          comp invs s
          ≅⟨ linvs ⟩ 
          iden ∎))
        (proof 
         comp m'' (comp s' s) 
         ≅⟨ sym ass ⟩ 
         comp (comp m'' s') s
         ≅⟨ cong (λ x → comp x s) p' ⟩ 
         comp m' s
         ≅⟨ p ⟩ 
         m ∎)
        (proof 
         comp f'' (comp s' s) 
         ≅⟨ sym ass ⟩ 
         comp (comp f'' s') s
         ≅⟨ cong (λ x → comp x s) q' ⟩ 
         comp f' s
         ≅⟨ q ⟩ 
         f ∎)

    Span~EqR : ∀{A B} → EqR (Span A B)
    Span~EqR = _~Span~_ , 
               record { 
                 refl  = ~refl; 
                 sym   = ~sym; 
                 trans = ~trans }

    idspan : {X : Obj} → Span X X
    idspan = record { 
      A' = _; 
      mhom = iden;
      fhom = iden;
      m∈ = iso idiso}

    compspan : {X Y Z : Obj} → Span Y Z → Span X Y → Span X Z
    compspan m'f' mf = 
      let open Pullback
          open Square
          open Span
          x = pul (fhom mf) (m∈ m'f')
          y = sq (proj₁ x)
      in record {
        A' = W y; 
        mhom = comp (mhom mf) (h y); 
        fhom = comp (fhom m'f') (k y); 
        m∈ = com (proj₂ x) (m∈ mf)}

    ~cong : {X Y Z : Obj}{mf m'f' : Span Y Z} → mf ~Span~ m'f' → 
                         {ng n'g' : Span X Y} → ng ~Span~ n'g' → 
                         compspan mf ng ~Span~ compspan m'f' n'g'
    ~cong {A}{B}{C}
          {mf}{m'f'}(spaneq s (invs ,, rinv ,, linv) ltri rtri)
          {ng}{n'g'}(spaneq s' (invs' ,, rinv' ,, linv') ltri' rtri') = 
      let open Pullback
          open Span mf   renaming (mhom to m;  fhom to f)
          open Span m'f' renaming (mhom to m'; fhom to f'; m∈ to m'∈)
          open Span ng   renaming (mhom to n;  fhom to g; m∈ to n∈)
          open Span n'g' renaming (mhom to n'; fhom to g'; m∈ to n'∈)
          p , h∈ = pul g m∈
          open Square (sq p) 
          p' , h'∈ = pul g' m'∈
          open Square (sq p') renaming (W to W';h to h'; k to k'; scom to scom')

          .hexcom : comp g' (comp s' h) ≅ comp m' (comp s k) 
          hexcom = 
            proof 
            comp g' (comp s' h) 
            ≅⟨ sym ass ⟩ 
            comp (comp g' s') h
            ≅⟨ cong (λ x → comp x h) rtri' ⟩ 
            comp g h
            ≅⟨ scom ⟩ 
            comp m k 
            ≅⟨ cong (λ x → comp x k) (sym ltri) ⟩ 
            comp (comp m' s) k 
            ≅⟨ ass ⟩ 
            comp m' (comp s k) 
            ∎

          hexsq : Square g' m'
          hexsq = record { 
            W = W; 
            h = comp s' h; 
            k = comp s k; 
            scom = hexcom }

          hexpul : Pullback g' m'
          hexpul = record { 
            sq   = hexsq; 
            prop = λ sq' → 
              let open Square sq' renaming (W to W''; 
                                            h to h''; 
                                            k to k'';
                                            scom to scom'')

                  .invrtri' : comp g invs' ≅ g'
                  invrtri' = proof 
                    comp g invs' 
                    ≅⟨ cong (λ x → comp x invs') (sym rtri') ⟩  
                    comp (comp g' s') invs' 
                    ≅⟨ ass ⟩  
                    comp g' (comp s' invs')
                    ≅⟨ cong (comp g') rinv' ⟩  
                    comp g' iden
                    ≅⟨ idr ⟩  
                    g' 
                    ∎
                  
                  .invltri : m' ≅ comp m invs
                  invltri = proof 
                    m' 
                    ≅⟨ sym idr ⟩ 
                    comp m' iden
                    ≅⟨ cong (comp m') (sym rinv) ⟩ 
                    comp m' (comp s invs)
                    ≅⟨ sym ass ⟩ 
                    comp (comp m' s) invs 
                    ≅⟨ cong (λ x → comp x invs) ltri ⟩ 
                    comp m invs 
                    ∎

                  .scom''' : comp g (comp invs' h'') ≅ comp m (comp invs k'') 
                  scom''' = 
                    proof 
                    comp g (comp invs' h'') 
                    ≅⟨ sym ass ⟩ 
                    comp (comp g invs') h''
                    ≅⟨ cong (λ x → comp x h'') invrtri' ⟩ 
                    comp g' h''
                    ≅⟨ scom'' ⟩ 
                    comp m' k''
                    ≅⟨ cong (λ x → comp x k'') invltri ⟩ 
                    comp (comp m invs) k''
                    ≅⟨ ass ⟩ 
                    comp m (comp invs k'') 
                    ∎
                  
                  sq'' : Square g m
                  sq'' = record { 
                    W = W''; 
                    h    = comp invs' h''; 
                    k    = comp invs k''; 
                    scom = scom''' }

                  pmap u' prop1 prop2 ,, pu' = prop p sq''

                  .prop1' : comp (comp s' h) u' ≅ h''
                  prop1' = proof 
                    comp (comp s' h) u' 
                    ≅⟨ ass ⟩ 
                    comp s' (comp h u')
                    ≅⟨ cong (comp s') prop1 ⟩ 
                    comp s' (comp invs' h'')
                    ≅⟨ sym ass ⟩ 
                    comp (comp s' invs') h''
                    ≅⟨ cong (λ x → comp x h'') rinv' ⟩ 
                    comp iden h''
                    ≅⟨ idl ⟩ 
                    h'' 
                    ∎ 

                  .prop2' : comp (comp s k) u' ≅ k''
                  prop2' = proof 
                    comp (comp s k) u' 
                    ≅⟨ ass ⟩ 
                    comp s (comp k u')
                    ≅⟨ cong (comp s) prop2 ⟩ 
                    comp s (comp invs k'')
                    ≅⟨ sym ass ⟩ 
                    comp (comp s invs) k''
                    ≅⟨ cong (λ x → comp x k'') rinv ⟩ 
                    comp iden k''
                    ≅⟨ idl ⟩ 
                    k'' 
                    ∎
                 -- using the constructor didn't work here...
              in record { mor = u'; prop1 = prop1'; prop2 = prop2' } 
                ,, 
                (λ u'' → 
                  let pmap u'' prop1'' prop2'' = u'' 

                      .prop1''' : comp h u'' ≅ comp invs' h''
                      prop1''' = proof 
                        comp h u'' 
                        ≅⟨ sym idl ⟩ 
                        comp iden (comp h u'' )
                        ≅⟨ cong (λ x → comp x (comp h u'')) (sym linv') ⟩ 
                        comp (comp invs' s') (comp h u'' )
                        ≅⟨ ass ⟩ 
                        comp invs' (comp s' (comp h u''))
                        ≅⟨ cong (comp invs') (sym ass) ⟩ 
                        comp invs' (comp (comp s' h) u'') 
                        ≅⟨ cong (comp invs') prop1'' ⟩ 
                        comp invs' h'' 
                        ∎

                      .prop2''' : comp k u'' ≅ comp invs k''
                      prop2''' = proof
                        comp k u'' 
                        ≅⟨ sym idl ⟩
                        comp iden (comp k u'')
                        ≅⟨ cong (λ x → comp x (comp k u'')) (sym linv) ⟩
                        comp (comp invs s) (comp k u'')
                        ≅⟨ ass ⟩
                        comp invs (comp s (comp k u''))
                        ≅⟨ cong (comp invs) (sym ass) ⟩
                        comp invs (comp (comp s k) u'')
                        ≅⟨ cong (comp invs) prop2'' ⟩
                        comp invs k''
                        ∎
                  in pu' (pmap u'' prop1''' prop2'''))} 

          iso = pullbackiso p' hexpul
          pmap u p1 p2 = fst (prop p' hexsq)

          .t1 : comp (comp n' h') u ≅ comp n h
          t1 = proof 
            comp (comp n' h') u 
            ≅⟨ ass ⟩ 
            comp n' (comp h' u)
            ≅⟨ cong (comp n') p1 ⟩ 
            comp n' (comp s' h)
            ≅⟨ sym ass ⟩ 
            comp (comp n' s') h
            ≅⟨ cong (λ x → comp x h) ltri' ⟩ 
            comp n h 
            ∎

          .t2 : comp (comp f' k') u ≅ comp f k
          t2 = proof 
            comp (comp f' k') u
            ≅⟨ ass ⟩ 
            comp f' (comp k' u)
            ≅⟨ cong (comp f') p2 ⟩ 
            comp f' (comp s k)
            ≅⟨ sym ass ⟩ 
            comp (comp f' s) k
            ≅⟨ cong (λ x → comp x k) rtri ⟩ 
            comp f k 
            ∎
          
      in spaneq u iso t1 t2

    .idlspan : {X Y : Obj} {mf : Span X Y} → compspan idspan mf ~Span~ mf
    idlspan {X}{Y}{mf} = 
      let open Pullback
          open Square
          open Span mf
      in spaneq 
      (h (sq (proj₁ (pul fhom (iso idiso))))) 
      (pullbackiso (trivialpul fhom) 
                     (proj₁ (pul fhom 
                                 (iso idiso)))) 
      refl 
      (scom (sq (proj₁ (pul fhom (iso idiso)))))

    .idrspan : {X Y : Obj} {mf : Span X Y} → compspan mf idspan ~Span~ mf
    idrspan {mf = mf} =
      let open Pullback
          open Square
          open Span mf
      in spaneq
      (k (sq (proj₁ (pul iden m∈)))) 
      (pullbackiso (sympul (trivialpul mhom))
                   (proj₁ (pul iden m∈)))
      (sym (scom (sq (proj₁ (pul iden m∈))))) 
      refl

    .assspan : {W X Y Z : Obj} 
      {m''f'' : Span Y Z} {m'f' : Span X Y} {mf : Span W X} →
      compspan (compspan m''f'' m'f') mf 
      ~Span~ 
      compspan m''f'' (compspan m'f' mf)
    assspan {m''f'' = m''f''} {m'f' = m'f'} {mf = mf} = 
      let open Span mf renaming (mhom to m; fhom to f)
          open Span m'f' renaming (mhom to m'; 
                                   fhom to f'; 
                                   m∈ to m'∈)
          open Span m''f'' renaming (mhom to m'';
                                     fhom to f'';
                                     m∈ to m''∈)

          bpul : Pullback f m'
          bpul = proj₁ (pul f m'∈)

          open Pullback bpul
          open Square sq renaming (W to B)

          b'pul : Pullback (comp f' k) m''
          b'pul = proj₁ (pul (comp f' k) m''∈)

          open Pullback b'pul renaming (sq to sq'; prop to prop')
          open Square sq' renaming (W to B'; 
                                    h to h'; 
                                    k to k'; 
                                    scom to scom')

          b''pul : Pullback f' m''
          b''pul = proj₁ (pul f' m''∈)

          open Pullback b''pul renaming (sq to sq''; prop to prop'')
          open Square sq'' renaming (W to B'';
                                     h to h'';
                                     k to k'';
                                     scom to scom'')

          b'''pul : Pullback f (comp m' h'')
          b'''pul = proj₁ (pul f (com (proj₂ (pul f' m''∈)) m'∈))

          open Pullback b'''pul renaming (sq to sq''';
                                          prop to prop''')
          open Square sq''' renaming (W to B'''; 
                                      h to h'''; 
                                      k to k'''; 
                                      scom to scom''')

          sqb' : Square f' m''
          sqb' = record { 
            W = B'; 
            h = comp k h'; 
            k = k'; 
            scom = 
              proof 
              comp f' (comp k h') 
              ≅⟨ sym ass ⟩ 
              comp (comp f' k) h' 
              ≅⟨ scom' ⟩ 
              comp m'' k' 
              ∎ }

          pu : PMap sqb' sq''
          pu = fst (prop'' sqb')

          open PMap pu renaming (mor to u)

          sqb''' : Square f m'
          sqb''' = record { 
            W = B'''; 
            h = h'''; 
            k = comp h'' k'''; 
            scom = 
              proof 
              comp f h''' 
              ≅⟨ scom''' ⟩ 
              comp (comp m' h'') k''' 
              ≅⟨ ass ⟩ 
              comp m' (comp h'' k''') 
              ∎ }

          pu' : PMap sqb''' sq
          pu' = fst (prop sqb''')

          open PMap pu' renaming (mor to u'; 
                                  prop1 to prop1'; 
                                  prop2 to prop2')

          upul : Pullback k h''
          upul = lem2 b'pul b''pul u (sym prop1) (sym prop2)

          u'pul : Pullback k h''
          u'pul = sympul (lem2 (sympul b'''pul) 
                               (sympul bpul) 
                               u'
                               (sym prop2')
                               (sym prop1'))

          open Pullback upul renaming (sq to usq ; prop to uprop)
          open Pullback u'pul renaming (sq to u'sq ; prop to u'prop)

          pα : PMap u'sq usq
          pα = fst (uprop u'sq)

          open PMap pα renaming (mor to α; 
                                 prop1 to prop1α; 
                                 prop2 to prop2α)

      in spaneq
        α 
        (pullbackiso upul u'pul) 
        (proof 
         comp (comp (comp m h) h') α 
         ≅⟨ ass ⟩ 
         comp (comp m h) (comp h' α)
         ≅⟨ cong (comp (comp m h)) prop1α ⟩ 
         comp (comp m h) u'
         ≅⟨ ass ⟩ 
         comp m (comp h u')
         ≅⟨ cong (comp m) prop1' ⟩ 
         comp m h'''
         ∎) 
        (proof 
         comp (comp f'' k') α
         ≅⟨ cong (λ y → comp (comp f'' y) α) (sym prop2) ⟩ 
         comp (comp f'' (comp k'' u)) α 
         ≅⟨ cong (λ y → comp y α) (sym ass) ⟩ 
         comp (comp (comp f'' k'') u) α
         ≅⟨ ass ⟩ 
         comp (comp f'' k'') (comp u α)
         ≅⟨ cong (comp (comp f'' k'')) prop2α ⟩ 
         comp (comp f'' k'') k'''
         ∎)    

    module _ (A B : Obj) where
      qspan = quot (Span A B) (Span~EqR)

      QSpan : Set
      QSpan = Quotient.Q qspan

    module _ {A B : Obj} where
      module Q = Quotient (qspan A B)

      compat : ∀{C} → (Span A B → C) → Set
      compat {C} = Q.compat {λ _ → C}

      abs : Span A B → QSpan A B
      abs = Q.abs

      lift : ∀{C}(f : Span A B → C) → .(compat f) → QSpan A B → C
      lift = Q.lift

      .ax1 : (mf m'f' : Span A B) → 
             mf ~Span~ m'f' → abs mf ≅ abs m'f'
      ax1 = Q.ax1

      ax2 : (mf m'f' : Span A B) → 
            abs mf ≅ abs m'f' → mf ~Span~ m'f'
      ax2 = Q.ax2

      .ax3 : ∀{C}(f : Span A B → C)(p : compat f)(mf : Span A B) → 
            (lift f p) (abs mf) ≅ f mf
      ax3  = Q.ax3

    open Lift₂

    qcomp : ∀{A B C} → QSpan B C → QSpan A B → QSpan A C
    qcomp {A}{B}{C} = lift₂ (qspan B C)
                            (qspan A B)
                            (λ x y → abs (compspan x y)) 
                            (λ p q → ax1 _ _ (~cong p q))

    .qcompabs : ∀{A B C}{mg : Span B C}{mf : QSpan A B}
                {p : compat (λ y → abs (compspan mg y))} → 
                qcomp (abs mg) mf ≅ lift (λ y → abs (compspan mg y)) p mf
    qcompabs {A}{B}{C}{mg}{mf} = lift₂→lift (qspan B C)
                                            (qspan A B)
                                            (λ x y → abs (compspan x y)) 
                                            (λ p q → ax1 _ _ (~cong p q)) 
                                            mg 
                                            mf

    .qcompabs' : ∀{A B C}{mg : QSpan B C}{mf : Span A B}
                 {p : compat (λ y → abs (compspan y mf))} → 
                 qcomp mg (abs mf) ≅ lift (λ y → abs (compspan y mf)) p mg
    qcompabs' {A}{B}{C}{mg}{mf} = lift₂→lift' (qspan B C)
                                              (qspan A B)
                                              (λ x y → abs (compspan x y)) 
                                              (λ p q → ax1 _ _ (~cong p q)) 
                                              mg 
                                              mf

    .qcompabsabs : ∀{A B C}{mg : Span B C}{mf : Span A B} → 
                   qcomp (abs mg) (abs mf) ≅ abs (compspan mg mf)
    qcompabsabs {A}{B}{C}{mg}{mf} = 
      proof
      qcomp (abs mg) (abs mf)
      ≅⟨ qcompabs ⟩
      lift (λ y → abs (compspan mg y)) (λ x → ax1 _ _ (~cong ~refl x)) (abs mf)
      ≅⟨ ax3 (λ y → abs (compspan mg y)) (λ x → ax1 _ _ (~cong ~refl x)) mf ⟩
      abs (compspan mg mf)
      ∎

    .qidlspan : ∀{A B}{mf : QSpan A B} → qcomp (abs idspan) mf ≅ mf
    qidlspan {A}{B}{mf} = 
      proof
      qcomp (abs idspan) mf 
      ≅⟨ qcompabs ⟩
      lift (λ y → abs (compspan idspan y)) (λ x → ax1 _ _ (~cong ~refl x)) mf
      ≅⟨ cong₂ {_}{_}{_}{_}{λ x₁ → {b₁ b' : Span A B} → b₁ ~Span~ b' → x₁ b₁ ≅ x₁ b'}{_}{_}{_}{λ x → ax1 _ _ (~cong ~refl x)}{ax1 _ _}(λ f (p : compat f) → lift f p mf)
           (ext (λ a → ax1 _ _ idlspan))
           (iext
            (λ a →
               iext
               (λ a₁ →
                  ext (λ a₂ → fixtypes' (ax1 _ _ idlspan))))) ⟩
      lift abs (ax1 _ _) mf
      ≅⟨ liftabs≅iden (qspan A B) mf ⟩
      mf
      ∎

    .qidrspan : ∀{A B}{mf : QSpan A B} → qcomp mf (abs idspan) ≅ mf
    qidrspan {A}{B}{mf} = 
      proof
      qcomp mf (abs idspan)
      ≅⟨ qcompabs' ⟩
      lift (λ a → abs (compspan a idspan)) (λ x → ax1 _ _ (~cong x ~refl)) mf
      ≅⟨ cong₂ {_}{_}{_}{_}{λ x₁ → {b₁ b' : Span A B} → b₁ ~Span~ b' → x₁ b₁ ≅ x₁ b'}{_}{_}{_}{λ x → ax1 _ _ (~cong x ~refl)}{ax1 _ _}(λ f (p : compat f) → lift f p mf) (ext (λ a → ax1 _ _ idrspan)) (iext (λ a → iext (λ a₁ → ext (λ a₂ → fixtypes' (ax1 _ _ idrspan))))) ⟩
      lift abs (ax1 _ _) mf
      ≅⟨ liftabs≅iden (qspan A B) mf ⟩
      mf
      ∎

    .qassspan : ∀{A B C D}{mh : QSpan C D}{mg : QSpan B C}{mf : QSpan A B} → 
                qcomp (qcomp mh mg) mf ≅ qcomp mh (qcomp mg mf)
    qassspan {A}{B}{C}{D}{mh}{mg}{mf} = 
      let open Quotient (qspan A B) renaming (lift to liftAB; abs to absAB; ax1 to ax1AB; ax3 to ax3AB)
          open Quotient (qspan A C) renaming (lift to liftAC; abs to absAC; ax1 to ax1AC; ax3 to ax3AC)
          open Quotient (qspan B C) renaming (lift to liftBC; abs to absBC; ax1 to ax1BC; ax3 to ax3BC)
          open Quotient (qspan C D) renaming (lift to liftCD; abs to absCD; ax1 to ax1CD)
      in liftCD {λ y → qcomp (qcomp y mg) mf ≅ qcomp y (qcomp mg mf)} 
                (λ a →
                  liftBC {λ y → qcomp (qcomp (absCD a) y) mf ≅ qcomp (absCD a) (qcomp y mf)}
                         (λ b → 
                           liftAB {λ y → qcomp (qcomp (absCD a) (absBC b)) y ≅ qcomp (absCD a) (qcomp (absBC b) y)}
                                  (λ c → proof
                                         qcomp (qcomp (absCD a) (absBC b)) (absAB c) 
                                         ≅⟨ cong (λ y → qcomp y (absAB c)) (qcompabs {_}{_}{_}{a}{absBC b}) ⟩
                                         qcomp (liftBC {λ _ → QSpan B D} (λ y → abs (compspan a y)) (λ x → ax1 _ _ (~cong ~refl x)) (absBC b)) (absAB c) 
                                         ≅⟨ cong (λ y → qcomp y (absAB c))
                                                 (ax3BC (λ y → abs (compspan a y)) (λ x → ax1 _ _ (~cong ~refl x)) b) ⟩
                                         qcomp (abs (compspan a b)) (absAB c) 
                                         ≅⟨ qcompabsabs ⟩
                                         abs (compspan (compspan a b) c) 
                                         ≅⟨ ax1 _ _ assspan ⟩
                                         abs (compspan a (compspan b c)) 
                                         ≅⟨ sym 
                                              (ax3AC (λ y → abs (compspan a y)) (λ x → ax1 _ _ (~cong ~refl x)) (compspan b c)) ⟩
                                         liftAC (λ y → abs (compspan a y)) (λ x → ax1 _ _ (~cong ~refl x)) (abs (compspan b c)) 
                                         ≅⟨ cong (liftAC (λ y → abs (compspan a y)) (λ x → ax1 _ _ (~cong ~refl x)))
                                                 (sym (ax3AB (λ y → abs (compspan b y)) (λ x → ax1 _ _ (~cong ~refl x)) c)) ⟩
                                         liftAC (λ y → abs (compspan a y)) (λ x → ax1 _ _ (~cong ~refl x)) (liftAB {λ _ → QSpan A C} (λ y → abs (compspan b y)) (λ x → ax1 _ _ (~cong ~refl x)) (absAB c))
                                         ≅⟨ cong (liftAC (λ y → abs (compspan a y)) (λ x → ax1 _ _ (~cong ~refl x))) (sym qcompabs) ⟩
                                         liftAC (λ y → abs (compspan a y)) (λ x → ax1 _ _ (~cong ~refl x)) (qcomp (absBC b) (absAB c)) 
                                         ≅⟨ sym qcompabs ⟩ 
                                         qcomp (absCD a) (qcomp (absBC b) (absAB c)) 
                                         ∎)
                         (λ x → fixtypes' (cong (qcomp (qcomp (absCD a) (absBC b))) (ax1AB _ _ x)))
                                         
                         mf) 
                  (λ x → fixtypes' (cong (λ y → qcomp (qcomp (absCD a) y) mf) (ax1BC _ _ x)))

                  mg)
               (λ x → fixtypes' (cong (λ y → qcomp (qcomp y mg) mf) (ax1CD _ _ x)))

               mh

    Par : Cat
    Par = record {
      Obj = Obj;
      Hom = QSpan;
      iden = abs idspan;
      comp = qcomp;
      idl = qidlspan;
      idr = qidrspan;
      ass = qassspan}
