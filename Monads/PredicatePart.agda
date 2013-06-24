{-# OPTIONS --type-in-type #-}
module Monads.PredicatePart where

open import Utilities
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Data.Product
open import Data.Unit
open import Categories
import Categories.Isos
open import Monads
open import Sets

open Cat Sets
open Categories.Isos Sets

prod≅ : {A : Set}{B : A → Set}{x y : Σ A B} → proj₁ x ≅ proj₁ y →
        proj₂ x ≅ proj₂ y → x ≅ y
prod≅ refl refl = refl

postulate iso≅ : ∀{X Y}(f : Hom X Y) → Iso f → X ≅ Y

postulate isoext : {X X' Y : Set}{f : Hom X Y}{g : Hom X' Y}{h : Hom X X'} →
                   Iso h → (∀{x} → f x ≅ (comp g h) x) → f ≅ g

pT : Set → Set
pT X = Σ Set (λ D → D → X)

pη : ∀{X} → X → pT X
pη x = ⊤ , (λ _ → x)

pbind : ∀{X Y}(f : X → pT Y) → pT X → pT Y
pbind f (D , g) = Σ D (proj₁ ∘ f ∘ g) , 
                  λ {(d , d') → proj₂ (f (g d)) d'}

plaw1 : ∀{X} → pbind (pη {X}) ≅ iden {pT X}
plaw1 = ext (λ {(d , g) → 
  prod≅ (iso≅ proj₁ ((λ x → x , _) ,, refl ,, refl)) 
         (isoext ((λ x → x , _) ,, refl ,, refl) (λ {_} → refl))})

plaw2 : ∀{X Y}{f : Hom X (pT Y)} → (pbind f) ∘ pη ≅ f
plaw2 {f = f} = ext (λ x → 
  let open Σ (f x) renaming (proj₁ to D; proj₂ to g)
  in prod≅ (iso≅ proj₂ ((λ x → _ , x) ,, refl ,, refl)) 
            (isoext ((λ x → _ , x) ,, refl ,, refl) (λ {_} → refl)))

plaw3 : ∀{X Y Z}{f : Hom X (pT Y)}{g : Hom Y (pT Z)} →
        pbind (comp (pbind g) f) ≅ comp (pbind g) (pbind f)
plaw3 {f = f} {g = g} = ext (λ a → 
    let open Σ a renaming (proj₁ to D; proj₂ to h)        
    in prod≅ 
       (iso≅ (λ {(d , d' , d'') → (d , d') , d''}) 
             ((λ {((d , d') , d'') → d , d' , d''}) ,, refl ,, refl))
       (isoext ((λ {((d , d') , d'') → d , (d' , d'')}) ,, refl ,, refl) 
               (λ {_} → refl)))

PredParMonad : Monad Sets
PredParMonad = record { 
  T = pT;
  η = pη; 
  bind = pbind; 
  law1 = plaw1;
  law2 = plaw2; 
  law3 = λ {_}{_}{_}{f}{g} → plaw3 {f = f} {g = g} }


-- new version with prop

prop : Set → Set
prop X = ∀{p q : X} → p ≅ q

postulate ⇔ : ∀{X Y} → prop X → prop Y → (X → Y) → (Y → X) → X ≅ Y

arg≅ : ∀{X Y}{f : X → Y}{x y : X} → x ≅ y → f x ≅ f y
arg≅ refl = refl

⇔m : ∀{X X' Y}{f : X → Y}{g : X' → Y} → prop X → prop X' → 
     (h : X → X') → (X' → X) → f ≅ g ∘ h → f ≅ g
⇔m p q h h' r with ⇔ p q h h'
⇔m {g = g} p q h h' r | refl = trans r (ext (λ x → arg≅ {_}{_}{g} p))

pT' : Set → Set
pT' X = Σ Set (λ D → (prop D) × (D → X))

pη' : ∀{X} → X → pT' X
pη' x = ⊤ , (λ {p}{q} → refl) , (λ _ → x)

dprod≅ : ∀{A}{B : A → Set}{x y : Σ A (λ a → B a)} → proj₁ x ≅ proj₁ y →
         (∀{a}{b b' : B a} → b ≅ b') → x ≅ y
dprod≅ {A}{B}{a , b}{.a , b'} refl q = prod≅ refl q

pbind' : ∀{X Y}(f : X → pT' Y) → pT' X → pT' Y
pbind' f (D , p , g) = (Σ D (proj₁ ∘ f ∘ g)) , 
                        (λ {q}{q'} → 
                          dprod≅ p (λ {d} → proj₁ (proj₂ (f (g d))))) , 
                        (λ {(d , d') → proj₂ (proj₂ (f (g d))) d'})

prod≅' : {A A' B B' : Set}{x : A × B}{y : A' × B'} → proj₁ x ≅ proj₁ y →
         proj₂ x ≅ proj₂ y → x ≅ y
prod≅' refl refl = refl

⊤prop : ∀{x y : ⊤} → x ≅ y
⊤prop = refl

{-
ext' : {A A' : Set}{B : A → A → Set}{B' : A' → A' → Set}
       {f : ∀{a a' : A} → B a a'}{g : ∀{a a' : A'} → B' a a'} → 
       (∀ a a' b b' → f {a}{b} ≅ g {a'}{b'}) → 
       ∀{a a' b b'} → f {a}{b} ≅ g {a'}{b'}
ext' p = λ {a}{a'}{b}{b'} → p a a' b b'

prop-irr : ∀{X Y} → (p : prop X) → (q : prop Y) → 
           ∀{x}{x'}{y}{y'} → p {x}{x'} ≅ q {y}{y'}
prop-irr {X}{Y} p q = {!!}
-}

plaw1' : ∀{X} → pbind' (pη' {X}) ≅ iden {pT' X}
plaw1' {X} = ext (λ x → 
  let pr : prop (proj₁ x)
      pr {p}{q} = (proj₁ (proj₂ x)) {p}{q}

      pr' : prop (Σ (proj₁ x) (λ _ → ⊤))
      pr' {p}{q} = dprod≅ (pr {proj₁ p}{proj₁ q}) ⊤prop
  in prod≅ (⇔ pr' pr proj₁ (λ y → y , tt))
           (prod≅' {!!}
                   (⇔m pr' pr proj₁ (λ y → y , tt) refl)))





{-
open import Data.Maybe
open import Data.Empty

Maybe→PredPart : ∀{X Y} → (X → Maybe Y) → X → pT Y
Maybe→PredPart f x with f x
Maybe→PredPart f x | just y = ⊤ , (λ _ → y)
Maybe→PredPart f x | nothing = ⊥ , ⊥-elim
-}


