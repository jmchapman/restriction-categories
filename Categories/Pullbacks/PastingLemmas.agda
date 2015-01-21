open import Categories

module Categories.Pullbacks.PastingLemmas (X : Cat) where

open import Utilities
open Cat X
open import Categories.Pullbacks X
open Pullback
open SqMap

pastingSq1 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X} → 
             Square (comp f f') g → Square f g
pastingSq1 {f = f}{g}{f'} (square W h k scom) = 
  record {
    W = W;
    h = comp f' h;
    k = k;
    scom = 
      proof 
      comp f (comp f' h) 
      ≅⟨ sym ass ⟩ 
      comp (comp f f') h
      ≅⟨ scom ⟩ 
      comp g k 
      ∎}

pastingSq2 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X} → 
             (p : Pullback f g) → Square f' (Square.h (sq p)) → 
             Square (comp f f') g
pastingSq2 {f = f}{g}{f'} (pullback (square W h k p) _) (square W' h' k' p') = 
  record {
    W    = W'; 
    h    = h';
    k    = comp k k';
    scom = 
      proof
      comp (comp f f') h'
      ≅⟨ ass ⟩
      comp f (comp f' h')
      ≅⟨ cong (comp f) p' ⟩
      comp f (comp h k')
      ≅⟨ sym ass ⟩
      comp (comp f h) k'
      ≅⟨ cong (λ f'' → comp f'' k') p ⟩
      comp (comp g k) k'
      ≅⟨ ass ⟩
      comp g (comp k k') 
      ∎ }

pasting1 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}(p : Pullback f g) → 
           {f' : Hom U X} → Pullback f' (Square.h (sq p)) → 
           Pullback (comp f f') g
pasting1 {f = f}{g} p {f'} q = 
  let pullback (square W h k scom) uniqPul = p
      pullback sq' uniqPul' = q
      square W' h' k' scom' = sq'
      prop : (sq'' : Square (comp f f') g) →
              Σ (SqMap sq'' (pastingSq2 p sq')) λ u → (u' : SqMap sq'' (pastingSq2 p sq')) → SqMap.sqMor u ≅ SqMap.sqMor u'
      prop r = 
        let square W'' h'' k'' scom'' = r
            sqmap u leftTru rightTru , s = uniqPul (pastingSq1 r)

            scomm' : _
            scomm' =
               proof comp f' h'' 
               ≅⟨ sym leftTru ⟩ 
               comp h u
               ∎

            m' : Square f' h
            m' = square W'' h'' u scomm'

            sqmap u' leftTr' rightTr' , s' = uniqPul' m' 

            prop2u' : _
            prop2u' =
              proof
              comp (comp k k') u'
              ≅⟨ ass ⟩ 
              comp k (comp k' u')
              ≅⟨ cong (comp k) rightTr' ⟩ 
              comp k u
              ≅⟨ rightTru ⟩ 
              k''
              ∎

            prop1p2 : (u'' : SqMap r (pastingSq2 p sq')) → comp h (comp k' (sqMor u'')) ≅ comp f' h''
            prop1p2 u'' =
              proof
              comp h (comp k' (sqMor u'')) 
              ≅⟨ sym ass ⟩
              comp (comp h k') (sqMor u'')
              ≅⟨ cong (λ f → comp f (sqMor u'')) (sym scom') ⟩
              comp (comp f' h') (sqMor u'')
              ≅⟨ ass ⟩
              comp f' (comp h' (sqMor u''))
              ≅⟨ cong (comp f') (leftTr u'') ⟩
              comp f' h'' 
              ∎

            prop2p2 : (u'' : SqMap r (pastingSq2 p sq')) → comp k (comp k' (sqMor u'')) ≅ k''
            prop2p2 u'' =
              proof
              comp k (comp k' (sqMor u'')) 
              ≅⟨ sym ass ⟩
              comp (comp k k') (sqMor u'') 
              ≅⟨ rightTr u'' ⟩ 
              k'' 
              ∎

            p2 : SqMap r (pastingSq2 p sq') → SqMap (pastingSq1 r) (sq p)    
            p2 u'' = sqmap (comp k' (sqMor u'')) (prop1p2 u'') (prop2p2 u'')

            p1 : SqMap r (pastingSq2 p sq') → SqMap m' (sq q)    
            p1 u'' = sqmap (sqMor u'') (leftTr u'') (sym (s (p2 u'')))
        in sqmap u' leftTr' prop2u' , 
           λ u'' → s' (p1 u'')
  in pullback (pastingSq2 p sq') prop

pasting2 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X}
           (r : Pullback (comp f f') g)(p : Pullback f g) → 
           (k' : Hom (Square.W (sq r)) (Square.W (sq p))) → 
           comp f' (Square.h (sq r)) ≅ comp (Square.h (sq p)) k' → 
           Square.k (sq r) ≅ comp (Square.k (sq p)) k' → 
           Pullback f' (Square.h (sq p))
pasting2 {f = f}{g}{f'} r p k' q q' = 
  let square W h k scom = sq p
      square W'' h'' k'' scom'' = sq r
  in record { 
    sq = square W'' h'' k' q;
  uniqPul = λ sq' → 
  let square W''' h''' k''' scom''' = sq'

      u : Σ (SqMap (pastingSq2 p sq') (sq r)) 
          λ u → (u' : SqMap (pastingSq2 p sq') (sq r)) → sqMor u ≅  sqMor u'
      u = uniqPul r (pastingSq2 p sq')

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
          ≅⟨ Square.scom (pastingSq2 p sq') ⟩
          comp g (comp k k''') 
          ∎ }

      u' : Σ (SqMap m' (sq p)) 
             λ u' → (u'' : SqMap m' (sq p)) → sqMor u' ≅  sqMor u''
      u' = uniqPul p m'

      k'u : SqMap m' (sq p)
      k'u = record { 
        sqMor = comp k' (sqMor (proj₁ u)); 
        leftTr = 
          proof 
          comp h (comp k' (sqMor (proj₁ u))) 
          ≅⟨ sym ass ⟩
          comp (comp h k') (sqMor (proj₁ u)) 
          ≅⟨ cong (λ f → comp f (sqMor (proj₁ u))) (sym q) ⟩ 
          comp (comp f' h'') (sqMor (proj₁ u)) 
          ≅⟨ ass ⟩ 
          comp f' (comp h'' (sqMor (proj₁ u))) 
          ≅⟨ cong (comp f') (leftTr (proj₁ u)) ⟩ 
          comp f' h''' 
          ∎; 
        rightTr = 
          proof 
          comp k (comp k' (sqMor (proj₁ u))) 
          ≅⟨ sym ass ⟩ 
          comp (comp k k') (sqMor (proj₁ u)) 
          ≅⟨ cong (λ f → comp f (sqMor (proj₁ u))) (sym q') ⟩ 
          comp k'' (sqMor (proj₁ u))
          ≅⟨ rightTr (proj₁ u) ⟩ 
          comp k k''' 
          ∎}
      
      pk'' : SqMap m' (sq p)
      pk'' = record { 
        sqMor = k'''; 
        leftTr = sym scom'''; 
        rightTr = refl}

  in record { 
    sqMor = sqMor (proj₁ u);
    leftTr = leftTr (proj₁ u); 
    rightTr = 
      proof
      comp k' (sqMor (proj₁ u)) 
      ≅⟨ sym (proj₂ u' k'u) ⟩
      sqMor (proj₁ u')
      ≅⟨ proj₂ u' pk'' ⟩
      k''' 
      ∎ }
    , 
    λ u'' → proj₂ u (record { 
      sqMor = sqMor u''; 
      leftTr = leftTr u''; 
      rightTr = 
        proof 
        comp k'' (sqMor u'')  
        ≅⟨ cong (λ f → comp f (sqMor u'')) q' ⟩ 
        comp (comp k k') (sqMor u'')
        ≅⟨ ass ⟩ 
        comp k (comp k' (sqMor u'')) 
        ≅⟨ cong (comp k) (rightTr u'') ⟩ 
        comp k k''' 
        ∎})}


{-
pastingSq2 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}(p : Pullback f g) →
            {f' : Hom U X} → Pullback f' (Square.h (sq p)) → 
            Square (comp f f') g
pastingSq2 {_}{_}{_}{_}{f}{g} p {f'} q = 
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
  
pastingSq1 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X} → 
              Square (comp f f') g → Square f g
pastingSq1 {_}{_}{_}{_}{f}{g}{f'} r = 
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
              Σ' (SqMap sq' (pastingSq2 p q)) λ u → (u' : SqMap sq' (pastingSq2 p q)) → SqMap.mor u ≅  SqMap.mor u'
      prop r = 
        let open Square (sq p)
            open Square (sq q) renaming (W to W'; h to h'; k to k'; scom to scom')
            open Square r renaming (W to W''; h to h''; k to k''; scom to scom'')

            u : Σ' (SqMap (pastingSq1 r) (sq p)) 
                (λ u → (u' : SqMap (pastingSq1 r) (sq p)) →  mor u ≅ mor u')
            u = prop p (pastingSq1 r)
     
            .scomm' : _
            scomm' =
               proof comp f' h'' 
               ≅⟨ sym (prop1 (proj₁ u)) ⟩ 
               comp h (mor (proj₁ u))
               ∎

            m' : Square f' h
            m' = record { 
              W    = W''; 
              h    = h''; 
              k    = mor (proj₁ u);
              scom = scomm' }

            u' : Σ' (SqMap m' (sq q)) 
                 (λ u₁ → (u' : SqMap m' (sq q)) → mor u₁ ≅ mor u')
            u' = prop q m'

            .prop2u' : _
            prop2u' =
              proof
              comp (comp k k') (mor (proj₁ u')) 
              ≅⟨ ass ⟩ 
              comp k (comp k' (mor (proj₁ u')))
              ≅⟨ cong (comp k) (prop2 (proj₁ u')) ⟩ 
              comp k (mor (proj₁ u))
              ≅⟨ prop2 (proj₁ u) ⟩ 
              k''
              ∎

            .prop1p2 : (u'' : SqMap r (pastingSq2 p q)) → comp h (comp k' (mor u'')) ≅ comp f' h''
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

            .prop2p2 : (u'' : SqMap r (pastingSq2 p q)) → comp k (comp k' (mor u'')) ≅ k''
            prop2p2 u'' =
                proof
                comp k (comp k' (mor u'')) 
                ≅⟨ sym ass ⟩
                comp (comp k k') (mor u'') 
                ≅⟨ prop2 u'' ⟩ 
                k'' 
                ∎

            p2 : SqMap r (pastingSq2 p q) → SqMap (pastingSq1 r) (sq p)    
            p2 u'' = 
              record {
                mor   = comp k' (mor u''); 
                prop1 = prop1p2 u''; 
                prop2 = prop2p2 u''}

            p1 : SqMap r (pastingSq2 p q) → SqMap m' (sq q)    
            p1 u'' = record { 
              mor = mor u''; 
              prop1 = prop1 u''; 
              prop2 = sym (proj₂ u (p2 u''))}
        in 
        record { 
          mor   = (mor (proj₁ u'));
          prop1 = prop1 (proj₁ u'); 
          prop2 = prop2u' }
        , 
        λ u'' → proj₂ u' (p1 u'')

  in record { 
    sq   = pastingSq2 p q; 
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
      u : Σ' (SqMap (m2 p sq') (sq r)) 
          λ u → (u' : SqMap (m2 p sq') (sq r)) → mor u ≅  mor u'
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
      u' : Σ' (SqMap m' (sq p)) 
             λ u' → (u'' : SqMap m' (sq p)) → mor u' ≅  mor u''
      u' = prop p m'

      k'u : SqMap m' (sq p)
      k'u = record { 
        mor = comp k' (mor (proj₁ u)); 
        prop1 = 
          proof 
          comp h (comp k' (mor (proj₁ u))) 
          ≅⟨ sym ass ⟩
          comp (comp h k') (mor (proj₁ u)) 
          ≅⟨ cong (λ f → comp f (mor (proj₁ u))) (sym q) ⟩ 
          comp (comp f' h'') (mor (proj₁ u)) 
          ≅⟨ ass ⟩ 
          comp f' (comp h'' (mor (proj₁ u))) 
          ≅⟨ cong (comp f') (prop1 (proj₁ u)) ⟩ 
          comp f' h''' 
          ∎; 
        prop2 = 
          proof 
          comp k (comp k' (mor (proj₁ u))) 
          ≅⟨ sym ass ⟩ 
          comp (comp k k') (mor (proj₁ u)) 
          ≅⟨ cong (λ f → comp f (mor (proj₁ u))) (sym q') ⟩ 
          comp k'' (mor (proj₁ u))
          ≅⟨ prop2 (proj₁ u) ⟩ 
          comp k k''' 
          ∎}
      
      pk'' : SqMap m' (sq p)
      pk'' = record { 
        mor = k'''; 
        prop1 = sym scom'''; 
        prop2 = refl}

  in record { 
    mor = mor (proj₁ u);
    prop1 = prop1 (proj₁ u); 
    prop2 = 
      proof
      comp k' (mor (proj₁ u)) 
      ≅⟨ sym (proj₂ u' k'u) ⟩
      mor (proj₁ u')
      ≅⟨ proj₂ u' pk'' ⟩
      k''' 
      ∎ }
    , 
     λ u'' → proj₂ u (record { 
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


-}
