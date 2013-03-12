open import Categories
module PullbacksLemmas (X : Cat) where
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Data.Product
open Cat X
open Monos X
open import Pullbacks X
open import Function

pullbackmonic : ∀{X Y Z}{f : Hom X Z}{g : Hom Y Z} → Mono g → 
                (q : Pullback f g) → Mono (Square.h (Pullback.sq q))
pullbackmonic {X}{Y}{Z}{f}{g} p q {A}{f₁}{f₂} r = 
  let m₁ : Square f g
      m₁ = record { 
        W    = A; 
        h    = comp (h sq) f₁; 
        k    = comp (k sq) f₁; 
        scom = 
          proof 
          comp f (comp (h sq) f₁) 
          ≅⟨ sym ass ⟩ 
          comp (comp f (h sq)) f₁
          ≅⟨ cong (λ f₃ → comp f₃ f₁) (scom sq) ⟩ 
          comp (comp g (k sq)) f₁
          ≅⟨ ass ⟩ 
          comp g (comp (k sq) f₁) 
          ∎ }
      m₂ : Square f g
      m₂ = record { 
        W    = A; 
        h    = comp (h sq) f₂; 
        k    = comp (k sq) f₂; 
        scom = 
          proof 
          comp f (comp (h sq) f₂) 
          ≅⟨ sym ass ⟩ 
          comp (comp f (h sq)) f₂
          ≅⟨ cong (λ f₃ → comp f₃ f₂) (scom sq) ⟩ 
          comp (comp g (k sq)) f₂
          ≅⟨ ass ⟩ 
          comp g (comp (k sq) f₂) 
          ∎} 

      lem : k m₁ ≅ k m₂
      lem = p $
        proof 
        comp g (comp (k sq) f₁)
        ≅⟨ sym (scom m₁) ⟩ 
        comp f (comp (h sq) f₁)
        ≅⟨ cong (comp f) r ⟩ 
        comp f (comp (h sq) f₂)
        ≅⟨ scom m₂ ⟩ 
        comp g (comp (k sq) f₂)
        ∎
      u = prop m₁

  in 
     proof 
     f₁ 
     ≅⟨ sym (proj₂ u (record { mor = f₁; prop1 = refl; prop2 = refl })) ⟩ 
     mor (proj₁ u)
     ≅⟨ proj₂ u (record { mor = f₂; prop1 = sym r; prop2 = sym lem}) ⟩ 
     f₂ 
     ∎
  where
  open Pullback q
  open Square
  open PMap

monic→pullback : ∀{X Z}{f : Hom X Z} → Mono f → Pullback f f
monic→pullback {X}{Z}{f} p = record { 
  sq = record { W = X; h = iden; k = iden; scom = refl }; 
  prop = λ sq' → (record { 
                    mor = h sq'; 
                    prop1 = idl; 
                    prop2 =
                      proof 
                      comp iden (h sq') 
                      ≅⟨ cong (comp iden) (p (scom sq')) ⟩ 
                      comp iden (k sq')
                      ≅⟨ idl ⟩ 
                      k sq'
                      ∎}) , 
                 (λ u' → 
                      proof 
                      h sq'
                      ≅⟨ sym (prop1 u') ⟩ 
                      comp iden (mor u')
                      ≅⟨ idl ⟩ 
                      mor u'
                      ∎)} 
  where
  open Square
  open PMap

easysquare : ∀{X Z}(f : Hom X Z) → Square f f
easysquare {X}{Z} f  = record { W = X; h = iden; k = iden; scom = refl }

pullback→mono : ∀{X Z}{f : Hom X Z} → 
                ((sq' : Square f f) → 
                 Σ (PMap sq' (easysquare f)) 
                   λ u → (u' : PMap sq' (easysquare f)) → 
                         PMap.mor u ≅  PMap.mor u') → Mono f
pullback→mono {X}{Z}{f} g {A}{f₁}{f₂} r = 
  let m : Square f f
      m = record { W = A; h = f₁; k = f₂; scom = r }
      u = proj₁ (g m)
  in
     proof 
     f₁ 
     ≅⟨ sym (prop1 u) ⟩
     comp iden (mor u) 
     ≅⟨ prop2 u ⟩
     f₂ 
     ∎
  where
  open PMap

open Isos X
open Square
open PMap

iso→pullback : ∀{X Y Z}{f : Hom X Z}{g : Hom Y Z} → Iso g → Pullback f g
iso→pullback {X}{Y}{Z}{f}{g} (g' , p , q) = record { 
  sq = record { 
    W = X;
    h = iden;
    k = comp g' f;
    scom = 
      proof 
      comp f iden 
      ≅⟨ idr ⟩ 
      f 
      ≅⟨ sym idl ⟩ 
      comp iden f 
      ≅⟨ cong (λ h → comp h f) (sym p) ⟩ 
      comp (comp g g') f 
      ≅⟨ ass ⟩ 
      comp g (comp g' f) 
      ∎ }; 
  prop = λ sq' → (record { 
                    mor = h sq'; 
                    prop1 = idl; 
                    prop2 = 
                      proof
                      comp (comp g' f) (h sq') 
                      ≅⟨ ass  ⟩ 
                      comp g' (comp f (h sq')) 
                      ≅⟨ cong (comp g') (scom sq') ⟩ 
                      comp g' (comp g (k sq')) 
                      ≅⟨ sym ass ⟩ 
                      comp (comp g' g) (k sq') 
                      ≅⟨ cong (λ f → comp f (k sq')) q ⟩ 
                      comp iden (k sq') 
                      ≅⟨ idl ⟩ 
                      k sq' 
                      ∎ }) , 
                  (λ u' →                      
                     proof 
                     h sq' 
                     ≅⟨ sym (prop1 u') ⟩ 
                     comp iden (mor u')
                     ≅⟨ idl ⟩ 
                     mor u'  
                     ∎)}
