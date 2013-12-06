open import Categories
module Categories.Pullbacks.PastingLemmas (X : Cat) where
  open import Utilities
  open Cat X
  open import Categories.Pullbacks X
  
  open Pullback
  open PMap

  bigsquare : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}(p : Pullback f g) →
              {f' : Hom U X} → Pullback f' (Square.h (sq p)) → 
              Square (comp f f') g
  bigsquare {_}{_}{_}{_}{f}{g} p {f'} q = 
    let open Square (sq p)
        open Square (sq q) renaming (W to W'; h to h'; k to k'; scom to scom')
  
        .scombs : _
        scombs =
          proof
          comp (comp f f') h' 
          ≅⟨ ass ⟩
          comp f (comp f' h') 
          ≅⟨ cong (comp f) scom' ⟩
          comp f (comp h k') 
          ≅⟨ sym ass ⟩
          comp (comp f h) k' 
          ≅⟨ cong (λ f'' → comp f'' k') scom ⟩
          comp (comp g k) k' 
          ≅⟨ ass ⟩
          comp g (comp k k') 
          ∎

    in record {
      W = W';
      h = h';
      k = comp k k';
      scom = scombs }
    
  smallsquare : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X} → 
                Square (comp f f') g → Square f g
  smallsquare {_}{_}{_}{_}{f}{g}{f'} r = 
    let open Square r 

        .scomss : _
        scomss =
          proof 
          comp f (comp f' h) 
          ≅⟨ sym ass ⟩ 
          comp (comp f f') h
          ≅⟨ scom ⟩ 
          comp g k 
          ∎

    in record { 
      W    = W; 
      h    = comp f' h; 
      k    = k; 
      scom = scomss } 

  lem1 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}(p : Pullback f g) → 
         {f' : Hom U X} → Pullback f' (Square.h (sq p)) → 
         Pullback (comp f f') g
  lem1 {_}{_}{_}{_}{f}{g} p {f'} q = 
    let         
        prop : (sq' : Square (comp f f') g) →
                Σ' (PMap sq' (bigsquare p q)) λ u → (u' : PMap sq' (bigsquare p q)) → PMap.mor u ≅  PMap.mor u'
        prop r = 
          let open Square (sq p)
              open Square (sq q) renaming (W to W'; h to h'; k to k'; scom to scom')
              open Square r renaming (W to W''; h to h''; k to k''; scom to scom'')

              u : Σ' (PMap (smallsquare r) (sq p)) 
                  (λ u → (u' : PMap (smallsquare r) (sq p)) →  mor u ≅ mor u')
              u = prop p (smallsquare r)
       
              .scomm' : _
              scomm' =
                 proof comp f' h'' 
                 ≅⟨ sym (prop1 (fst u)) ⟩ 
                 comp h (mor (fst u))
                 ∎

              m' : Square f' h
              m' = record { 
                W    = W''; 
                h    = h''; 
                k    = mor (fst u);
                scom = scomm' }

              u' : Σ' (PMap m' (sq q)) 
                   (λ u₁ → (u' : PMap m' (sq q)) → mor u₁ ≅ mor u')
              u' = prop q m'
  
              .prop2u' : _
              prop2u' =
                proof
                comp (comp k k') (mor (fst u')) 
                ≅⟨ ass ⟩ 
                comp k (comp k' (mor (fst u')))
                ≅⟨ cong (comp k) (prop2 (fst u')) ⟩ 
                comp k (mor (fst u))
                ≅⟨ prop2 (fst u) ⟩ 
                k''
                ∎
  
              .prop1p2 : (u'' : PMap r (bigsquare p q)) → comp h (comp k' (mor u'')) ≅ comp f' h''
              prop1p2 u'' =
                  proof
                  comp h (comp k' (mor u'')) 
                  ≅⟨ sym ass ⟩
                  comp (comp h k') (mor u'')
                  ≅⟨ cong (λ f → comp f (mor u'')) (sym scom') ⟩
                  comp (comp f' h') (mor u'')
                  ≅⟨ ass ⟩
                  comp f' (comp h' (mor u''))
                  ≅⟨ cong (comp f') (prop1 u'') ⟩
                  comp f' h'' 
                  ∎

              .prop2p2 : (u'' : PMap r (bigsquare p q)) → comp k (comp k' (mor u'')) ≅ k''
              prop2p2 u'' =
                  proof
                  comp k (comp k' (mor u'')) 
                  ≅⟨ sym ass ⟩
                  comp (comp k k') (mor u'') 
                  ≅⟨ prop2 u'' ⟩ 
                  k'' 
                  ∎

              p2 : PMap r (bigsquare p q) → PMap (smallsquare r) (sq p)    
              p2 u'' = 
                record {
                  mor   = comp k' (mor u''); 
                  prop1 = prop1p2 u''; 
                  prop2 = prop2p2 u''}

              p1 : PMap r (bigsquare p q) → PMap m' (sq q)    
              p1 u'' = record { 
                mor = mor u''; 
                prop1 = prop1 u''; 
                prop2 = sym (snd u (p2 u''))}
          in 
          record { 
            mor   = (mor (fst u'));
            prop1 = prop1 (fst u'); 
            prop2 = prop2u' }
          ,, 
          λ u'' → snd u' (p1 u'')

    in record { 
      sq   = bigsquare p q; 
      prop = prop}


  m2 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X} → 
       (p : Pullback f g) → Square f' (Square.h (sq p)) → 
       Square (comp f f') g
  m2 {_}{_}{_}{_}{f}{g}{f'} p sq' = 
    let open Square (sq p)
        open Square sq' renaming (W to W'; h to h'; k to k'; scom to scom')
    in record {
      W    = W'; 
      h    = h';
      k    = comp k k';
      scom = 
        proof
        comp (comp f f') h'
        ≅⟨ ass ⟩
        comp f (comp f' h')
        ≅⟨ cong (comp f) scom' ⟩
        comp f (comp h k')
        ≅⟨ sym ass ⟩
        comp (comp f h) k'
        ≅⟨ cong (λ f'' → comp f'' k') scom ⟩
        comp (comp g k) k'
        ≅⟨ ass ⟩
        comp g (comp k k') 
        ∎ }


  lem2 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X}
         (r : Pullback (comp f f') g)(p : Pullback f g) → 
         (k' : Hom (Square.W (sq r)) (Square.W (sq p))) → 
         comp f' (Square.h (sq r)) ≅ comp (Square.h (sq p)) k' → 
         Square.k (sq r) ≅ comp (Square.k (sq p)) k' → 
         Pullback f' (Square.h (sq p))
  lem2 {_}{_}{_}{_}{f}{g}{f'} r p k' q q' = 
    let open Square (sq p) 
        open Square (sq r) renaming (W to W''; 
                                     h to h''; 
                                     k to k''; 
                                     scom to scom'')
    in record { 
      sq   = record { 
        W    = W''; 
        h    = h''; 
        k    = k'; 
        scom = q }; 
    prop = λ sq' → 
    let open Square sq' renaming (W to W'''; 
                                    h to h'''; 
                                    k to k'''; 
                                    scom to scom''')
        u : Σ' (PMap (m2 p sq') (sq r)) 
            λ u → (u' : PMap (m2 p sq') (sq r)) → mor u ≅  mor u'
        u = prop r (m2 p sq')

        m' : Square f g
        m' = record { 
          W    = W'''; 
          h    = comp f' h'''; 
          k    = comp k k''';
          scom = 
            proof
            comp f (comp f' h''') 
            ≅⟨ sym ass ⟩
            comp (comp f f') h'''
            ≅⟨ Square.scom (m2 p sq') ⟩
            comp g (comp k k''') 
            ∎ }
        u' : Σ' (PMap m' (sq p)) 
               λ u' → (u'' : PMap m' (sq p)) → mor u' ≅  mor u''
        u' = prop p m'

        k'u : PMap m' (sq p)
        k'u = record { 
          mor = comp k' (mor (fst u)); 
          prop1 = 
            proof 
            comp h (comp k' (mor (fst u))) 
            ≅⟨ sym ass ⟩
            comp (comp h k') (mor (fst u)) 
            ≅⟨ cong (λ f → comp f (mor (fst u))) (sym q) ⟩ 
            comp (comp f' h'') (mor (fst u)) 
            ≅⟨ ass ⟩ 
            comp f' (comp h'' (mor (fst u))) 
            ≅⟨ cong (comp f') (prop1 (fst u)) ⟩ 
            comp f' h''' 
            ∎; 
          prop2 = 
            proof 
            comp k (comp k' (mor (fst u))) 
            ≅⟨ sym ass ⟩ 
            comp (comp k k') (mor (fst u)) 
            ≅⟨ cong (λ f → comp f (mor (fst u))) (sym q') ⟩ 
            comp k'' (mor (fst u))
            ≅⟨ prop2 (fst u) ⟩ 
            comp k k''' 
            ∎}
        
        pk'' : PMap m' (sq p)
        pk'' = record { 
          mor = k'''; 
          prop1 = sym scom'''; 
          prop2 = refl}

    in record { 
      mor = mor (fst u);
      prop1 = prop1 (fst u); 
      prop2 = 
        proof
        comp k' (mor (fst u)) 
        ≅⟨ sym (snd u' k'u) ⟩
        mor (fst u')
        ≅⟨ snd u' pk'' ⟩
        k''' 
        ∎ }
      ,, 
       λ u'' → snd u (record { 
         mor = mor u''; 
         prop1 = prop1 u''; 
         prop2 = proof 
           comp k'' (mor u'')  
           ≅⟨ cong (λ f → comp f (mor u'')) q' ⟩ 
           comp (comp k k') (mor u'')
           ≅⟨ ass ⟩ 
           comp k (comp k' (mor u'')) 
           ≅⟨ cong (comp k) (prop2 u'') ⟩ 
           comp k k''' 
           ∎})}


