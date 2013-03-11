open import Categories
module Pullbacks (X : Cat) where
  open import Relation.Binary.HeterogeneousEquality
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Data.Product
  open Cat X

  record Square {X Y Z}(f : Hom X Z)(g : Hom Y Z) : Set where
     field W    : Obj
           h    : Hom W X
           k    : Hom W Y
           scom : comp f h ≅ comp g k
  open Square

  record PMap  {X Y Z : Obj}{f : Hom X Z}{g : Hom Y Z}(sq' sq : Square f g) : Set where
    field mor   : Hom (W sq') (W sq)
          prop1 : comp (h sq) mor ≅ h sq'
          prop2 : comp (k sq) mor ≅ k sq'
  open PMap

  record Pullback {X Y Z}(f : Hom X Z)(g : Hom Y Z) : Set where
    field sq : Square f g
          prop : (sq' : Square f g) → Σ (PMap sq' sq) λ u → (u' : PMap sq' sq) → mor u ≅  mor u'
  open Pullback

  open Isos X

  pullbackiso : ∀{X Y Z}{f : Hom X Z}{g : Hom Y Z}(p p' : Pullback f g) → Iso (mor (proj₁ (prop p (sq p'))))
  pullbackiso {X}{Y}{Z}{f}{g} p p' = 
    let u = prop p (sq p)
        u⁻¹ = prop p' (sq p')

        idenp : PMap (sq p) (sq p)
        idenp = record { mor = iden; prop1 = idr; prop2 = idr }

        compp : PMap (sq p) (sq p)
        compp = record { 
          mor = comp (mor (proj₁ (prop p (sq p')))) (mor (proj₁ (prop p' (sq p)))); 
          prop1 = 
            proof 
            comp (h (sq p)) (comp (mor (proj₁ (prop p (sq p')))) (mor (proj₁ (prop p' (sq p))))) 
            ≅⟨ sym ass ⟩ 
            comp (comp (h (sq p)) (mor (proj₁ (prop p (sq p'))))) (mor (proj₁ (prop p' (sq p))))
            ≅⟨ cong (λ g → comp g (mor (proj₁ (prop p' (sq p))))) (prop1 (proj₁ (prop p (sq p')))) ⟩ 
            comp (h (sq p')) (mor (proj₁ (prop p' (sq p))))
            ≅⟨ prop1 (proj₁ (prop p' (sq p))) ⟩ 
            h (sq p) 
            ∎;
          prop2 = proof 
            comp (k (sq p)) (comp (mor (proj₁ (prop p (sq p')))) (mor (proj₁ (prop p' (sq p))))) 
            ≅⟨ sym ass ⟩ 
            comp (comp (k (sq p)) (mor (proj₁ (prop p (sq p'))))) (mor (proj₁ (prop p' (sq p))))
            ≅⟨ cong (λ g → comp g (mor (proj₁ (prop p' (sq p))))) (prop2 (proj₁ (prop p (sq p')))) ⟩ 
            comp (k (sq p')) (mor (proj₁ (prop p' (sq p))))
            ≅⟨ prop2 (proj₁ (prop p' (sq p))) ⟩ 
            k (sq p) 
            ∎}

        idenp' : PMap (sq p') (sq p')
        idenp' = record { mor = iden; prop1 = idr; prop2 = idr }

        compp' : PMap (sq p') (sq p')
        compp' = record { 
          mor = comp (mor (proj₁ (prop p' (sq p)))) (mor (proj₁ (prop p (sq p')))); 
          prop1 = 
            proof 
            comp (h (sq p')) (comp (mor (proj₁ (prop p' (sq p)))) (mor (proj₁ (prop p (sq p'))))) 
            ≅⟨ sym ass ⟩ 
            comp (comp (h (sq p')) (mor (proj₁ (prop p' (sq p))))) (mor (proj₁ (prop p (sq p'))))
            ≅⟨ cong (λ g → comp g (mor (proj₁ (prop p (sq p'))))) (prop1 (proj₁ (prop p' (sq p)))) ⟩ 
            comp (h (sq p)) (mor (proj₁ (prop p (sq p'))))
            ≅⟨ prop1 (proj₁ (prop p (sq p'))) ⟩ 
            h (sq p') 
            ∎;
          prop2 = proof 
            comp (k (sq p')) (comp (mor (proj₁ (prop p' (sq p)))) (mor (proj₁ (prop p (sq p'))))) 
            ≅⟨ sym ass ⟩ 
            comp (comp (k (sq p')) (mor (proj₁ (prop p' (sq p))))) (mor (proj₁ (prop p (sq p'))))
            ≅⟨ cong (λ g → comp g (mor (proj₁ (prop p (sq p'))))) (prop2 (proj₁ (prop p' (sq p)))) ⟩ 
            comp (k (sq p)) (mor (proj₁ (prop p (sq p'))))
            ≅⟨ prop2 (proj₁ (prop p (sq p'))) ⟩ 
            k (sq p') 
            ∎}

    in (mor (proj₁ (prop p' (sq p)))) , 
       (proof 
        comp (mor (proj₁ (prop p (sq p')))) (mor (proj₁ (prop p' (sq p))))
        ≅⟨ sym (proj₂ u compp) ⟩ 
        mor (proj₁ u)
        ≅⟨ proj₂ u idenp ⟩ 
        iden
        ∎) , 
       (proof 
        comp (mor (proj₁ (prop p' (sq p)))) (mor (proj₁ (prop p (sq p'))))
        ≅⟨ sym (proj₂ u⁻¹ compp') ⟩ 
        mor (proj₁ u⁻¹)
        ≅⟨ proj₂ u⁻¹ idenp' ⟩ 
        iden
        ∎) 

  -- pasting lemmas
  bigsquare : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}(p : Pullback f g) →
              {f' : Hom U X} → Pullback f' (h (sq p)) → Square (comp f f') g
  bigsquare {_}{_}{_}{_}{f}{g} p {f'} q = record {
    W = W (sq q);
    h = h (sq q);
    k = comp (k (sq p)) (k (sq q));
    scom = 
      proof
      comp (comp f f') (h (sq q)) ≅⟨ ass ⟩
      comp f (comp f' (h (sq q))) ≅⟨ cong (comp f) (scom (sq q)) ⟩
      comp f (comp (h (sq p)) (k (sq q))) ≅⟨ sym ass ⟩
      comp (comp f (h (sq p))) (k (sq q)) ≅⟨
      cong (λ f'' → comp f'' (k (sq q))) (scom (sq p)) ⟩
      comp (comp g (k (sq p))) (k (sq q)) ≅⟨ ass ⟩
      comp g (comp (k (sq p)) (k (sq q))) 
      ∎ }

  m : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X} → 
      Square (comp f f') g → Square f g
  m {_}{_}{_}{_}{f}{g}{f'} r = record { 
    W    = W r; 
    h    = comp f' (h r); 
    k    = k r; 
    scom = 
      proof 
      comp f (comp f' (h r)) 
      ≅⟨ sym ass ⟩ 
      comp (comp f f') (h r)
      ≅⟨ scom r ⟩ 
      comp g (k r) 
      ∎ } 


  lem1 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}(p : Pullback f g) → 
         {f' : Hom U X} → Pullback f' (h (sq p)) → Pullback (comp f f') g
  lem1 {_}{_}{_}{_}{f}{g} p {f'} q = record { 
    sq   = bigsquare p q; 
    prop = λ r → 
      let 
        u : Σ (PMap (m r) (sq p)) 
              (λ u → (u' : PMap (m r) (sq p)) →  mor u ≅ mor u')
        u = prop p (m r)
        m' : Square f' (h (sq p))
        m' = record { 
          W    = W r; 
          h    = h r; 
          k    = mor (proj₁ u);
          scom = 
            proof comp f' (h r) 
            ≅⟨ sym (prop1 (proj₁ u)) ⟩ 
            comp (h (sq p)) (mor (proj₁ u))
            ∎ }
        u' : Σ (PMap m' (sq q)) 
               (λ u₁ → (u' : PMap m' (sq q)) → mor u₁ ≅ mor u')
        u' = prop q m'
      in 
       (record { 
         mor   = (mor (proj₁ u'));
         prop1 = prop1 (proj₁ u'); 
         prop2 = 
           proof
           comp (comp (k (sq p)) (k (sq q))) (mor (proj₁ u')) 
           ≅⟨ ass ⟩ 
           comp (k (sq p)) (comp (k (sq q)) (mor (proj₁ u')))
           ≅⟨ cong (comp (k (sq p))) (prop2 (proj₁ u')) ⟩ 
           comp (k (sq p)) (mor (proj₁ u))
           ≅⟨ prop2 (proj₁ u) ⟩ 
           k r 
           ∎ })
       , 
       λ u'' → proj₂ u' (record { 
          mor   = mor u''; 
          prop1 = prop1 u''; 
          prop2 = sym (proj₂ u (record {
            mor   = comp (k (sq q)) (mor u''); 
            prop1 = 
              proof
              comp (h (sq p)) (comp (k (sq q)) (mor u'')) 
              ≅⟨ sym ass ⟩
              comp (comp (h (sq p)) (k (sq q))) (mor u'')
              ≅⟨ cong (λ f₁ → comp f₁ (mor u'')) (sym (scom (sq q))) ⟩
              comp (comp f' (h (sq q))) (mor u'')
              ≅⟨ ass ⟩
              comp f' (comp (h (sq q)) (mor u''))
              ≅⟨ cong (comp f') (prop1 u'') ⟩
              comp f' (h r) 
              ∎; 
            prop2 = 
              proof
              comp (k (sq p)) (comp (k (sq q)) (mor u'')) 
              ≅⟨ sym ass ⟩
              comp (comp (k (sq p)) (k (sq q))) (mor u'') 
              ≅⟨ prop2 u'' ⟩ 
              k r ∎ }))})}

  m2 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X} → 
       (p : Pullback f g) → Square f' (h (sq p)) → 
       Square (comp f f') g
  m2 {_}{_}{_}{_}{f}{g}{f'} p sq' = record { 
    W    = W sq'; 
    h    = h sq';
    k    = comp (k (sq p)) (k sq');
    scom = 
      proof
      comp (comp f f') (h sq')
      ≅⟨ ass ⟩
      comp f (comp f' (h sq'))
      ≅⟨ cong (comp f) (scom sq') ⟩
      comp f (comp (h (sq p)) (k sq'))
      ≅⟨ sym ass ⟩
      comp (comp f (h (sq p))) (k sq')
      ≅⟨ cong (λ f'' → comp f'' (k sq')) (scom (sq p)) ⟩
      comp (comp g (k (sq p))) (k sq')
      ≅⟨ ass ⟩
      comp g (comp (k (sq p)) (k sq')) 
      ∎ }

  lem2 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X}
         (r : Pullback (comp f f') g)(p : Pullback f g) → 
         (k' : Hom (W (sq r)) (W (sq p))) → 
         comp f' (h (sq r)) ≅ comp (h (sq p)) k' → 
         k (sq r) ≅ comp (k (sq p)) k' → 
         Pullback f' (h (sq p))
  lem2 {_}{_}{_}{_}{f}{g}{f'} r p k' q q' = record { 
    sq   = record { 
      W    = W (sq r); 
      h    = h (sq r); 
      k    = k'; 
      scom = q }; 
    prop = λ sq' → let
        u : Σ (PMap (m2 p sq') (sq r)) 
            λ u → (u' : PMap (m2 p sq') (sq r)) → mor u ≅  mor u'
        u = prop r (m2 p sq')

        m' : Square f g
        m' = record { 
          W    = W sq'; 
          h    = comp f' (h sq'); 
          k    = comp (k (sq p)) (k sq');
          scom = 
            proof
            comp f (comp f' (h sq')) 
            ≅⟨ sym ass ⟩
            comp (comp f f') (h sq')
            ≅⟨ scom (m2 p sq') ⟩
            comp g (comp (k (sq p)) (k sq')) 
            ∎ }
        u' : Σ (PMap m' (sq p)) 
               λ u' → (u'' : PMap m' (sq p)) → mor u' ≅  mor u''
        u' = prop p m'

        k'u : PMap m' (sq p)
        k'u = record { 
          mor = comp k' (mor (proj₁ u)); 
          prop1 = proof 
                  comp (h (sq p)) (comp k' (mor (proj₁ u))) 
                  ≅⟨ sym ass ⟩
                  comp (comp (h (sq p)) k') (mor (proj₁ u)) 
                  ≅⟨ cong (λ f → comp f (mor (proj₁ u))) (sym q) ⟩ 
                  comp (comp f' (h (sq r))) (mor (proj₁ u)) 
                  ≅⟨ ass ⟩ 
                  comp f' (comp (h (sq r)) (mor (proj₁ u))) 
                  ≅⟨ cong (comp f') (prop1 (proj₁ u)) ⟩ 
                  comp f' (h sq') 
                  ∎; 
          prop2 = proof 
                  comp (k (sq p)) (comp k' (mor (proj₁ u))) 
                  ≅⟨ sym ass ⟩ 
                  comp (comp (k (sq p)) k') (mor (proj₁ u)) 
                  ≅⟨ cong (λ f → comp f (mor (proj₁ u))) (sym q') ⟩ 
                  comp (k (sq r)) (mor (proj₁ u))
                  ≅⟨ prop2 (proj₁ u) ⟩ 
                  comp (k (sq p)) (k sq') 
                  ∎}
        
        k'' : PMap m' (sq p)
        k'' = record { 
          mor = k sq'; 
          prop1 = sym (scom sq'); 
          prop2 = refl}

    in record { 
         mor = mor (proj₁ u);
         prop1 = prop1 (proj₁ u); 
         prop2 = 
           proof
           comp k' (mor (proj₁ u)) 
           ≅⟨ sym (proj₂ u' k'u) ⟩
           mor (proj₁ u')
           ≅⟨ proj₂ u' k'' ⟩
           k sq' 
           ∎ }
      , 
      (λ u'' → proj₂ u (record { 
         mor = mor u''; 
         prop1 = prop1 u''; 
         prop2 = proof 
           comp (k (sq r)) (mor u'')  
           ≅⟨ cong (λ f → comp f (mor u'')) q' ⟩ 
           comp (comp (k (sq p)) k') (mor u'')
           ≅⟨ ass ⟩ 
           comp (k (sq p)) (comp k' (mor u'')) 
           ≅⟨ cong (comp (k (sq p))) (prop2 u'') ⟩ 
           comp (k (sq p)) (k sq') 
           ∎}))}

  trivialpul : ∀{X Y}(f : Hom X Y) → Pullback f iden
  trivialpul {X}{Y} f = record { 
    sq = record { 
      W = X; 
      h = iden; 
      k = f; 
      scom = 
        proof 
        comp f iden 
        ≅⟨ idr ⟩ 
        f 
        ≅⟨ sym idl ⟩ 
        comp iden f 
        ∎}; 
    prop = λ sq' → 
      (record { 
         mor = h sq'; 
         prop1 = idl; 
         prop2 = proof comp f (h sq') ≅⟨ scom sq' ⟩ comp iden (k sq') ≅⟨ idl ⟩ k sq' ∎  }) , 
      (λ u' → proof h sq' ≅⟨ sym (prop1 u') ⟩ comp iden (mor u') ≅⟨ idl ⟩ mor u' ∎) }
