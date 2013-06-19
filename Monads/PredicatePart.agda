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


prod≅ : ∀{X}{a b : Σ Set (λ D → D → X)} → proj₁ a ≅ proj₁ b → 
        proj₂ a ≅ proj₂ b → a ≅ b
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

ParMonad : Monad Sets
ParMonad = record { 
  T = pT;
  η = pη; 
  bind = pbind; 
  law1 = plaw1;
  law2 = plaw2; 
  law3 = λ {_}{_}{_}{f}{g} → plaw3 {f = f} {g = g} }

{-
ParMonad : Monad Sets
ParMonad = record { 
  T = λ A → Σ Set (λ D → D → A); 
  η = λ {A} a → ⊤ , (λ _ → a); 
  bind = λ {A}{B} pf pg → 
    let open Σ pg renaming (proj₁ to P; proj₂ to g)
        f = comp proj₁ pf
    in Σ P (λ p → (comp f g) p) , 
       λ pq → 
         let open Σ pq renaming (proj₁ to p; proj₂ to q)
             open Σ ((comp pf g) p) renaming (proj₁ to Q; proj₂ to h)
         in h q;
  law1 = λ {X} → ext (λ a → 
    let open Σ a renaming (proj₁ to P; proj₂ to g)

        π₁ : Σ P (λ _ → ⊤) → P
        π₁ = proj₁

        π₁iso : Iso π₁
        π₁iso = record { 
          inv = λ x → x , _; 
          rinv = refl; 
          linv = refl }

        eq : Σ P (λ _ → ⊤) ≅ P
        eq = iso≅ π₁ π₁iso

    in prod≅ 
       (iso≅ π₁ π₁iso) 
       (isoext π₁iso (λ {_} → refl)));

  law2 = λ {X} {Y} {f} → ext (λ a → 
    let open Σ (f a) renaming (proj₁ to P; proj₂ to g)

        π₂ : Σ ⊤ (λ _ → P) → P
        π₂ = proj₂

        π₂iso : Iso π₂
        π₂iso = record { 
          inv = λ x → _ , x; 
          rinv = refl; 
          linv = refl }

    in prod≅ 
      (iso≅ π₂ π₂iso) 
      (isoext π₂iso (λ {_} → refl)));
  law3 = λ {X} {Y} {Z} {f} {g} → ext (λ a → 
    let open Σ a renaming (proj₁ to P; proj₂ to h)        
    in prod≅ 
       (iso≅ 
        ((λ px → 
            let open Σ px renaming (proj₁ to p; proj₂ to x)
            in (p , proj₁ x) , proj₂ x)) 
        (record { 
          inv = λ px → 
            let open Σ px renaming (proj₁ to p; proj₂ to x) 
            in (proj₁ p) , ((proj₂ p) , x); 
          rinv = refl; 
          linv = refl }))
       (isoext 
        (record { 
          inv = λ px → 
            let open Σ px renaming (proj₁ to p; proj₂ to x) 
            in (proj₁ p) , ((proj₂ p) , x); 
          rinv = refl; 
          linv = refl })
        (λ {_} → refl)))}
-}