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

  record PMap  {X Y Z : Obj}{f : Hom X Z}{g : Hom Y Z}(sq' sq : Square f g) 
         : Set where
    open Square
    field mor   : Hom (W sq') (W sq)
          prop1 : comp (h sq) mor ≅ h sq'
          prop2 : comp (k sq) mor ≅ k sq'
  open PMap


  record Pullback {X Y Z}(f : Hom X Z)(g : Hom Y Z) : Set where
    field sq : Square f g
          prop : (sq' : Square f g) → 
                 Σ (PMap sq' sq) λ u → (u' : PMap sq' sq) → mor u ≅  mor u'
  open Pullback

  open Isos X

  pullbackiso : ∀{X Y Z}{f : Hom X Z}{g : Hom Y Z}(p p' : Pullback f g) → 
                Iso (mor (proj₁ (prop p (sq p'))))
  pullbackiso {X}{Y}{Z}{f}{g} p p' = 
    let u   = prop p (sq p)
        u⁻¹ = prop p' (sq p')
        u₁  = proj₁ (prop p' (sq p))
        u₂  = proj₁ (prop p (sq p'))

        idenp : PMap (sq p) (sq p)
        idenp = record { mor = iden; prop1 = idr; prop2 = idr }

        compp : PMap (sq p) (sq p)
        compp = record { 
          mor = comp (mor u₂) (mor u₁); 
          prop1 = 
            proof 
            comp (h (sq p)) (comp (mor u₂) (mor u₁)) 
            ≅⟨ sym ass ⟩ 
            comp (comp (h (sq p)) (mor u₂)) (mor u₁)
            ≅⟨ cong (λ g → comp g (mor u₁)) (prop1 u₂) ⟩ 
            comp (h (sq p')) (mor u₁)
            ≅⟨ prop1 u₁ ⟩ 
            h (sq p) 
            ∎;
          prop2 = proof 
            comp (k (sq p)) (comp (mor u₂) (mor u₁)) 
            ≅⟨ sym ass ⟩ 
            comp (comp (k (sq p)) (mor u₂)) (mor u₁)
            ≅⟨ cong (λ g → comp g (mor u₁)) (prop2 u₂) ⟩ 
            comp (k (sq p')) (mor u₁)
            ≅⟨ prop2 u₁ ⟩ 
            k (sq p) 
            ∎}

        idenp' : PMap (sq p') (sq p')
        idenp' = record { mor = iden; prop1 = idr; prop2 = idr }

        compp' : PMap (sq p') (sq p')
        compp' = record { 
          mor = comp (mor u₁) (mor u₂); 
          prop1 = 
            proof 
            comp (h (sq p')) (comp (mor u₁) (mor u₂)) 
            ≅⟨ sym ass ⟩ 
            comp (comp (h (sq p')) (mor u₁)) (mor u₂)
            ≅⟨ cong (λ g → comp g (mor u₂)) (prop1 u₁) ⟩ 
            comp (h (sq p)) (mor u₂)
            ≅⟨ prop1 u₂ ⟩ 
            h (sq p') 
            ∎;
          prop2 = proof 
            comp (k (sq p')) (comp (mor u₁) (mor u₂)) 
            ≅⟨ sym ass ⟩ 
            comp (comp (k (sq p')) (mor u₁)) (mor u₂)
            ≅⟨ cong (λ g → comp g (mor u₂)) (prop2 u₁) ⟩ 
            comp (k (sq p)) (mor u₂)
            ≅⟨ prop2 u₂ ⟩ 
            k (sq p') 
            ∎}

    in mor u₁ 
       , 
       (proof 
        comp (mor u₂) (mor u₁)
        ≅⟨ sym (proj₂ u compp) ⟩ 
        mor (proj₁ u)
        ≅⟨ proj₂ u idenp ⟩ 
        iden
        ∎) 
       , 
       (proof 
        comp (mor u₁) (mor u₂)
        ≅⟨ sym (proj₂ u⁻¹ compp') ⟩ 
        mor (proj₁ u⁻¹)
        ≅⟨ proj₂ u⁻¹ idenp' ⟩ 
        iden
        ∎) 
    where open Square

  -- pasting lemmas
  bigsquare : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}(p : Pullback f g) →
              {f' : Hom U X} → Pullback f' (Square.h (sq p)) → 
              Square (comp f f') g
  bigsquare {_}{_}{_}{_}{f}{g} p {f'} q = 
    let open Square (sq p)
        open Square (sq q) renaming (W to W'; h to h'; k to k'; scom to scom')
    in record {
      W = W';
      h = h';
      k = comp k k';
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
    
    
    

  smallsquare : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}{f' : Hom U X} → 
                Square (comp f f') g → Square f g
  smallsquare {_}{_}{_}{_}{f}{g}{f'} r = 
    let open Square r 
    in record { 
      W    = W; 
      h    = comp f' h; 
      k    = k; 
      scom = 
        proof 
        comp f (comp f' h) 
        ≅⟨ sym ass ⟩ 
        comp (comp f f') h
        ≅⟨ scom ⟩ 
        comp g k 
        ∎ } 

  lem1 : ∀{U X Y Z}{f : Hom X Z}{g : Hom Y Z}(p : Pullback f g) → 
         {f' : Hom U X} → Pullback f' (Square.h (sq p)) → 
         Pullback (comp f f') g
  lem1 {_}{_}{_}{_}{f}{g} p {f'} q = record { 
    sq   = bigsquare p q; 
    prop = λ r → 
    let open Square (sq p)
        open Square (sq q) renaming (W to W'; h to h'; k to k'; scom to scom')
        open Square r renaming (W to W''; h to h''; k to k''; scom to scom'')
        u : Σ (PMap (smallsquare r) (sq p)) 
              (λ u → (u' : PMap (smallsquare r) (sq p)) →  mor u ≅ mor u')
        u = prop p (smallsquare r)
        m' : Square f' h
        m' = record { 
          W    = W''; 
          h    = h''; 
          k    = mor (proj₁ u);
          scom = 
            proof comp f' h'' 
            ≅⟨ sym (prop1 (proj₁ u)) ⟩ 
            comp h (mor (proj₁ u))
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
           comp (comp k k') (mor (proj₁ u')) 
           ≅⟨ ass ⟩ 
           comp k (comp k' (mor (proj₁ u')))
           ≅⟨ cong (comp k) (prop2 (proj₁ u')) ⟩ 
           comp k (mor (proj₁ u))
           ≅⟨ prop2 (proj₁ u) ⟩ 
           k''
           ∎ })
       , 
       λ u'' → proj₂ u' (record { 
          mor   = mor u''; 
          prop1 = prop1 u''; 
          prop2 = sym (proj₂ u (record {
            mor   = comp k' (mor u''); 
            prop1 = 
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
              ∎; 
            prop2 = 
              proof
              comp k (comp k' (mor u'')) 
              ≅⟨ sym ass ⟩
              comp (comp k k') (mor u'') 
              ≅⟨ prop2 u'' ⟩ 
              k'' 
              ∎}))})}


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
        u : Σ (PMap (m2 p sq') (sq r)) 
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
        u' : Σ (PMap m' (sq p)) 
               λ u' → (u'' : PMap m' (sq p)) → mor u' ≅  mor u''
        u' = prop p m'

        k'u : PMap m' (sq p)
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
        
        pk'' : PMap m' (sq p)
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
      let open Square sq'
      in record { 
         mor = h; 
         prop1 = idl; 
         prop2 = proof comp f h ≅⟨ scom ⟩ comp iden k ≅⟨ idl ⟩ k ∎  } , 
      λ u' → 
        proof 
        h 
        ≅⟨ sym (prop1 u') ⟩ 
        comp iden (mor u') 
        ≅⟨ idl ⟩ 
        mor u'
        ∎}

  trivialpul2 : ∀{X Y}(f : Hom X Y) → Pullback iden f
  trivialpul2 {X}{Y} f = record { 
    sq = record { 
      W = X; 
      h = f; 
      k = iden; 
      scom = 
        proof 
        comp iden f 
        ≅⟨ idl ⟩ 
        f 
        ≅⟨ sym idr ⟩ 
        comp f iden 
        ∎}; 
    prop = λ sq' →
      let open Square sq'
      in record { 
         mor = k; 
         prop1 = 
           proof 
           comp f k 
           ≅⟨ sym scom ⟩ 
           comp iden h 
           ≅⟨ idl ⟩ 
           h 
           ∎; 
         prop2 = idl } , 
      λ u' → 
        proof 
        k 
        ≅⟨ sym (prop2 u') ⟩ 
        comp iden (mor u') 
        ≅⟨ idl ⟩ 
        mor u' 
        ∎}
