{-# OPTIONS --type-in-type #-}
module Categories where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Data.Product

record Cat : Set where
  field Obj  : Set
        Hom  : Obj → Obj → Set
        iden : ∀{X} → Hom X X
        comp : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → comp iden f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → comp f iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
               comp (comp f g) h ≅ comp f (comp g h)

module Monos (X : Cat) where
  open Cat X

  Mono : ∀{A B} → Hom A B → Set
  Mono f = ∀{C}{g h : Hom C _} → comp f g ≅ comp f h → g ≅ h

  idmono : ∀{A} → Mono (iden {A})
  idmono {A}{C}{g}{h} p = 
    proof
    g 
    ≅⟨ sym idl ⟩ 
    comp iden g 
    ≅⟨ p ⟩ 
    comp iden h 
    ≅⟨ idl ⟩ 
    h 
    ∎

module Isos (X : Cat) where
  open Cat X

  Iso : ∀{A B} → Hom A B → Set
  Iso {A}{B} f = Σ (Hom B A) (λ g → comp f g ≅ iden {B} × comp g f ≅ iden {A})


  invuniq : ∀{A B}(f : Hom A B)(p q : Iso f) → proj₁ p ≅ proj₁ q
  invuniq f (g , p , p') (g' , q , q') = 
    proof 
    g 
    ≅⟨ sym idr ⟩ 
    comp g iden
    ≅⟨ cong (comp g) (sym q) ⟩ 
    comp g (comp f g')
    ≅⟨ sym ass ⟩ 
    comp (comp g f) g'
    ≅⟨ cong (λ h → comp h g') p' ⟩     
    comp iden g'
    ≅⟨ idl ⟩     
    g'
    ∎


module Pullbacks (X : Cat) where
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
        u' : Σ (PMap m' (sq q)) (λ u₁ → (u' : PMap m' (sq q)) → mor u₁ ≅ mor u')
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

_Op : Cat → Cat
C Op = record {
  Obj  = Obj; 
  Hom  = λ X Y → Hom Y X;
  iden = iden;
  comp = λ f g → comp g f; 
  idl  = idr;
  idr  = idl;
  ass  = sym ass}
  where open Cat C
