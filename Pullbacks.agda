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

        compmor : Hom (Square.W (sq p)) (Square.W (sq p))
        compmor = comp (mor u₂) (mor u₁)

        compprop1 = 
            proof 
            comp (h (sq p)) (comp (mor u₂) (mor u₁)) 
            ≅⟨ sym ass ⟩ 
            comp (comp (h (sq p)) (mor u₂)) (mor u₁)
            ≅⟨ cong (λ g → comp g (mor u₁)) (prop1 u₂) ⟩ 
            comp (h (sq p')) (mor u₁)
            ≅⟨ prop1 u₁ ⟩ 
            h (sq p) 
            ∎

        compprop2 = 
            proof 
            comp (k (sq p)) (comp (mor u₂) (mor u₁)) 
            ≅⟨ sym ass ⟩ 
            comp (comp (k (sq p)) (mor u₂)) (mor u₁)
            ≅⟨ cong (λ g → comp g (mor u₁)) (prop2 u₂) ⟩ 
            comp (k (sq p')) (mor u₁)
            ≅⟨ prop2 u₁ ⟩ 
            k (sq p) 
            ∎


        compp : PMap (sq p) (sq p)
        compp = record { 
          mor = compmor;
          prop1 = compprop1;
          prop2 = compprop2}

        idenp' : PMap (sq p') (sq p')
        idenp' = record { mor = iden; prop1 = idr; prop2 = idr }

        compmor' : Hom (Square.W (sq p')) (Square.W (sq p'))
        compmor' = comp (mor u₁) (mor u₂) 

        compprop1' = 
            proof 
            comp (h (sq p')) (comp (mor u₁) (mor u₂)) 
            ≅⟨ sym ass ⟩ 
            comp (comp (h (sq p')) (mor u₁)) (mor u₂)
            ≅⟨ cong (λ g → comp g (mor u₂)) (prop1 u₁) ⟩ 
            comp (h (sq p)) (mor u₂)
            ≅⟨ prop1 u₂ ⟩ 
            h (sq p') 
            ∎

        compprop2' =
            proof 
            comp (k (sq p')) (comp (mor u₁) (mor u₂)) 
            ≅⟨ sym ass ⟩ 
            comp (comp (k (sq p')) (mor u₁)) (mor u₂)
            ≅⟨ cong (λ g → comp g (mor u₂)) (prop2 u₁) ⟩ 
            comp (k (sq p)) (mor u₂)
            ≅⟨ prop2 u₂ ⟩ 
            k (sq p') 
            ∎

        compp' : PMap (sq p') (sq p')
        compp' = record { 
          mor = compmor';
          prop1 = compprop1';
          prop2 = compprop2'}
        
        isoproof1 =
          proof 
          comp (mor u₂) (mor u₁)
          ≅⟨ sym (proj₂ u compp) ⟩ 
          mor (proj₁ u)
          ≅⟨ proj₂ u idenp ⟩ 
          iden
          ∎

        isoproof2 =
          proof 
          comp (mor u₁) (mor u₂)
          ≅⟨ sym (proj₂ u⁻¹ compp') ⟩ 
          mor (proj₁ u⁻¹)
          ≅⟨ proj₂ u⁻¹ idenp' ⟩ 
          iden
          ∎

    in mor u₁ 
       , 
       isoproof1
       , 
       isoproof2 
    where open Square

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

  sympul : ∀{X Y Z}{f : Hom X Z}{g : Hom Y Z} → Pullback f g → Pullback g f
  sympul {X}{Y}{Z}{f}{g} p = 
    let open Square (sq p)
    in record { 
      sq = record { W = W; h = k; k = h; scom = sym scom }; 
      prop = λ sq' → 
        let open Square sq' renaming (W to W' ; h to h' ; k to k' ; scom to scom')
            
            symsq' : Square f g
            symsq' = record { W = W'; h = k'; k = h'; scom = sym scom' }

            pu : PMap symsq' (sq p)
            pu = proj₁ (prop p symsq')

            open PMap pu renaming (mor to u ; prop1 to uprop1 ; prop2 to uprop2)

        in record { 
             mor = u; 
             prop1 = uprop2; 
             prop2 = uprop1 } , 
           λ pu' → 
             let open PMap pu' renaming (mor to u' ; prop1 to u'prop1 ; prop2 to u'prop2)

                 sympu' : PMap symsq' (sq p)
                 sympu' = record { 
                   mor = u'; 
                   prop1 = u'prop2; 
                   prop2 = u'prop1 }
             in proj₂ (prop p symsq') sympu' }
