
module RestrictionPred where

open import Relation.Binary.HeterogeneousEquality
open import Utilities
open import Function
open import Categories
open import RestrictionCat
open import Data.Product
open import Monads
open import Monads.Kleisli
open import Sets
open import Monads.PredicatePart
open import Categories.Isos

open Cat (Kl PredPar)

prest : ∀{X Y} → (X → pT Y) → X → pT X
prest f x = proj₁ (f x) , proj₁ (proj₂ (f x)) , (λ _ → x)

pR1 : {A B : Obj}{f : Hom A B} → comp f (prest f) ≅ f
pR1 {X}{Y}{f} = ext (λ x →
  let pr : prop (proj₁ (f x))
      pr p q = (proj₁ (proj₂ (f x))) p q

      pr' : prop (Σ (proj₁ (f x)) (λ y → proj₁ (f x)))
      pr' p q = dprod≅ (pr (proj₁ p) (proj₁ q)) 
                       (λ _ y y' → pr y y')

  in prod≅ (⇔ pr' pr proj₁ (λ y → y , y)) 
           (prod≅' (⇔p pr' pr proj₁ (λ y → y , y)) 
                   (⇔m pr' pr proj₂ (λ y → y , y) refl)))

pR2 : {X Y Z : Obj}{f : Hom X Y}{g : Hom X Z} → 
      comp (prest f) (prest g) ≅ comp (prest g) (prest f)
pR2 {f = f}{g = g} = ext (λ x → 
  let pr : prop (Σ (proj₁ (g x)) (λ x₁ → proj₁ (f x)))
      pr p q = dprod≅ ((proj₁ (proj₂ (g x))) (proj₁ p) (proj₁ q))
                       (λ _ p' q' → (proj₁ (proj₂ (f x))) p' q')

      pr' : prop (Σ (proj₁ (f x)) (λ x₁ → proj₁ (g x)))
      pr' p q = dprod≅ ((proj₁ (proj₂ (f x))) (proj₁ p) (proj₁ q))
                        (λ _ p' q' → (proj₁ (proj₂ (g x))) p' q')
      
  in prod≅ (⇔ pr pr' (λ {(x , y) → y , x}) (λ {(x , y) → y , x}))
           (prod≅' (⇔p pr pr' (λ {(x , y) → y , x}) (λ {(x , y) → y , x})) 
                   (⇔m pr 
                       pr' 
                       (λ {(x , y) → y , x}) 
                       (λ {(x , y) → y , x}) 
                       refl)))


trasl : ∀{X Y Z}(f : X → pT Y)(g : Y → pT Z)(x : X) →
        (y w : proj₁ (f x)) → proj₁ (g (proj₂ (proj₂ (f x)) w)) → 
         proj₁ (g (proj₂ (proj₂ (f x)) y))
trasl f g x y w r with prf f x y w
trasl f g x .w w r | refl = r

pR4 : {X Y Z : Obj}{f : Hom X Y}{g : Hom Y Z} →
      comp (prest g) f ≅ comp f (prest (comp g f))
pR4 {f = f}{g = g} = ext (λ x → 
  let pr : prop (Σ (proj₁ (f x)) (λ x₁ → proj₁ (g (proj₂ (proj₂ (f x)) x₁))))
      pr p q = dprod≅ (proj₁ (proj₂ (f x)) (proj₁ p) (proj₁ q)) 
                      (λ y p' q' → (proj₁ (proj₂ (g (proj₂ (proj₂ (f x)) y)))) 
                                   p' 
                                   q')
      
      pr' : prop (Σ (Σ (proj₁ (f x)) 
                       (λ y → proj₁ (g (proj₂ (proj₂ (f x)) y)))) 
                    (λ y → proj₁ (f x)))
      pr' p q = 
        dprod≅ (dprod≅ (proj₁ (proj₂ (f x)) (proj₁ (proj₁ p)) (proj₁ (proj₁ q)))
                       (λ y p' q' → 
                         proj₁ (proj₂ (g (proj₂ (proj₂ (f x)) y))) p' q')) 
               (λ _ p' q' → proj₁ (proj₂ (f x)) p' q')

  in prod≅ (⇔ pr 
              pr' 
              (λ {(y , z) → (y , z) , y}) 
              (λ {((y , z) , w) → w , trasl f g x w y z}))
           (prod≅' (⇔p pr 
                       pr'
                       (λ {(y , z) → (y , z) , y}) 
                       (λ {((y , z) , w) → w , trasl f g x w y z})) 
                   (⇔m pr 
                       pr' 
                       (λ {(y , z) → (y , z) , y}) 
                       (λ {((y , z) , w) → w , trasl f g x w y z}) 
                       refl)))

PredParRestCat : RestCat
PredParRestCat = record { 
  cat = Kl PredPar; 
  rest = prest;
  R1 = pR1;
  R2 = λ {_}{_}{_}{f}{g} → pR2 {_}{_}{_}{f}{g};
  R3 = refl;
  R4 = λ {_}{_}{_}{f}{g} → pR4 {_}{_}{_}{f}{g}}

