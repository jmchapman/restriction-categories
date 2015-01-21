{-# OPTIONS --type-in-type #-}
open import Categories

module Categories.Pullbacks (X : Cat) where

open import Utilities
open Cat X
open import Categories.Isos X

record Square {X Y Z}(f : Hom X Z)(g : Hom Y Z) : Set where
  constructor square
  field W    : Obj
        h    : Hom W X
        k    : Hom W Y
        scom : comp f h ≅ comp g k

record SqMap {X Y Z : Obj}{f : Hom X Z}{g : Hom Y Z}
             (sq' sq : Square f g) : Set where
  constructor sqmap
  open Square
  field sqMor     : Hom (W sq') (W sq)
        leftTr   : comp (h sq) sqMor ≅ h sq'
        rightTr  : comp (k sq) sqMor ≅ k sq'

open SqMap

record Pullback {X Y Z}(f : Hom X Z)(g : Hom Y Z) : Set where
  constructor pullback
  field sq      : Square f g
        uniqPul : (sq' : Square f g) → 
                  Σ (SqMap sq' sq) 
                     λ u → (u' : SqMap sq' sq) → sqMor u ≅ sqMor u'

open Pullback

trivialPullback : ∀{X Y}(f : Hom X Y) → Pullback f iden
trivialPullback f = record {
  sq = square _ iden f (proof comp f iden ≅⟨ idr ⟩ f ≅⟨ sym idl ⟩ comp iden f ∎) ;
  uniqPul = λ {(square W h k p) → 
    sqmap h idl (proof comp f h ≅⟨ p ⟩ comp iden k ≅⟨ idl ⟩ k ∎) ,
    λ u' → 
      proof 
      h 
      ≅⟨ sym (leftTr u') ⟩ 
      comp iden (sqMor u') 
      ≅⟨ idl ⟩ 
      sqMor u'
      ∎}}

pullbackIso : ∀{X Y Z}{f : Hom X Z}{g : Hom Y Z}
              (p p' : Pullback f g) → 
              Iso (sqMor (proj₁ (uniqPul p (sq p'))))
pullbackIso p p' = 
  let open Square
      u   = uniqPul p (sq p)
      u⁻¹ = uniqPul p' (sq p')
      u₁  = proj₁ (uniqPul p' (sq p))
      u₂  = proj₁ (uniqPul p (sq p'))

      idenp : SqMap (sq p) (sq p)
      idenp = sqmap iden idr idr

      compsqMor : Hom (Square.W (sq p)) (Square.W (sq p))
      compsqMor = comp (sqMor u₂) (sqMor u₁)

      compleftTr : _
      compleftTr = 
          proof 
          comp (h (sq p)) (comp (sqMor u₂) (sqMor u₁)) 
          ≅⟨ sym ass ⟩ 
          comp (comp (h (sq p)) (sqMor u₂)) (sqMor u₁)
          ≅⟨ cong (λ g → comp g (sqMor u₁)) (leftTr u₂) ⟩ 
          comp (h (sq p')) (sqMor u₁)
          ≅⟨ leftTr u₁ ⟩ 
          h (sq p) 
          ∎

      comprightTr : _
      comprightTr = 
          proof 
          comp (k (sq p)) (comp (sqMor u₂) (sqMor u₁)) 
          ≅⟨ sym ass ⟩ 
          comp (comp (k (sq p)) (sqMor u₂)) (sqMor u₁)
          ≅⟨ cong (λ g → comp g (sqMor u₁)) (rightTr u₂) ⟩ 
          comp (k (sq p')) (sqMor u₁)
          ≅⟨ rightTr u₁ ⟩ 
          k (sq p) 
          ∎

      compp : SqMap (sq p) (sq p)
      compp = sqmap compsqMor compleftTr comprightTr

      idenp' : SqMap (sq p') (sq p')
      idenp' = sqmap iden idr idr

      compsqMor' : Hom (Square.W (sq p')) (Square.W (sq p'))
      compsqMor' = comp (sqMor u₁) (sqMor u₂) 

      compleftTr' : _
      compleftTr' = 
          proof 
          comp (h (sq p')) (comp (sqMor u₁) (sqMor u₂)) 
          ≅⟨ sym ass ⟩ 
          comp (comp (h (sq p')) (sqMor u₁)) (sqMor u₂)
          ≅⟨ cong (λ g → comp g (sqMor u₂)) (leftTr u₁) ⟩ 
          comp (h (sq p)) (sqMor u₂)
          ≅⟨ leftTr u₂ ⟩ 
          h (sq p') 
          ∎

      comprightTr' : _
      comprightTr' =
          proof 
          comp (k (sq p')) (comp (sqMor u₁) (sqMor u₂)) 
          ≅⟨ sym ass ⟩ 
          comp (comp (k (sq p')) (sqMor u₁)) (sqMor u₂)
          ≅⟨ cong (λ g → comp g (sqMor u₂)) (rightTr u₁) ⟩ 
          comp (k (sq p)) (sqMor u₂)
          ≅⟨ rightTr u₂ ⟩ 
          k (sq p') 
          ∎

      compp' : SqMap (sq p') (sq p')
      compp' = sqmap compsqMor' compleftTr' comprightTr'
      
      isoproof1 : _
      isoproof1 =
        proof 
        comp (sqMor u₂) (sqMor u₁)
        ≅⟨ sym (proj₂ u compp) ⟩ 
        sqMor (proj₁ u)
        ≅⟨ proj₂ u idenp ⟩ 
        iden
        ∎

      isoproof2 : _
      isoproof2 =
        proof 
        comp (sqMor u₁) (sqMor u₂)
        ≅⟨ sym (proj₂ u⁻¹ compp') ⟩ 
        sqMor (proj₁ u⁻¹)
        ≅⟨ proj₂ u⁻¹ idenp' ⟩ 
        iden
        ∎
  in iso (sqMor u₁) isoproof1 isoproof2

symPullback : ∀{X Y Z}{f : Hom X Z}{g : Hom Y Z} → Pullback f g → Pullback g f
symPullback (pullback (square W h k p) uniqPul) = record { 
  sq = square W k h (sym p); 
  uniqPul = λ {(square W' h' k' p') → 
    let sqmap u l r , h = uniqPul (square W' k' h' (sym p'))
    in sqmap u r l , λ {(sqmap u' l' r') → h (sqmap u' r' l') }}}
