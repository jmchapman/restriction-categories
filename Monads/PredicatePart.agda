open import Level

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

open Cat {suc (suc zero)}{suc zero} Sets
open Categories.Isos {suc (suc zero)}{suc zero} Sets

-- various products equality proofs

prod≅ : ∀{a b}{A : Set a}{B : A → Set b}{x y : Σ A B} → proj₁ x ≅ proj₁ y →
        proj₂ x ≅ proj₂ y → x ≅ y
prod≅ refl refl = refl

prod≅' : ∀{a b}{A A' : Set a}{B B' : Set b}{x : A × B}{y : A' × B'} → 
         proj₁ x ≅ proj₁ y → proj₂ x ≅ proj₂ y → x ≅ y
prod≅' refl refl = refl

dprod≅ : ∀{a b}{A : Set a}{B : A → Set b}{x y : Σ A B} → proj₁ x ≅ proj₁ y →
         (∀(a : A)(b b' : B a) → b ≅ b') → x ≅ y
dprod≅ {_}{_}{_}{_}{.a , b}{a , b'} refl q = prod≅ refl (q a b b')

-- squash type

prop : Set → Set
prop X = ∀(p q : X) → p ≅ q

⊤prop : ∀{x y : ⊤} → x ≅ y
⊤prop = refl

-- equality for the squash type

postulate ⇔ : ∀{X Y} → prop X → prop Y → (X → Y) → (Y → X) → X ≅ Y

⇔m : ∀{a}{X X' : Set}{Y : Set a}{f : X → Y}{g : X' → Y} → prop X → prop X' → 
     (h : X → X') → (X' → X) → f ≅ g ∘ h → f ≅ g
⇔m p q h h' r with ⇔ p q h h'
⇔m {g = g} p q h h' r | refl = trans r (ext (λ x → cong g (p (h x) x)))

⇔p : ∀{X X'}(p : prop X)(q : prop X')(h : X → X') → (X' → X) → p ≅ q
⇔p p q h h' with ⇔ p q h h'
⇔p {X}{.X} p q h h' | refl = ext (λ x → 
  ext (λ y → ≡-to-≅ (proof-irrelevance (p x y) (q x y))))

-- predicate partiality monad

pT : Set₁ → Set₁
pT X = Σ Set (λ D → prop D × (D → X))

pη : ∀{X} → X → pT X
pη x = ⊤ , (λ p q → refl) , (λ _ → x)

pbind : ∀{X Y}(f : X → pT Y) → pT X → pT Y
pbind f (D , p , g) = 
  (Σ D (proj₁ ∘ f ∘ g)) , 
  (λ {(d , d') (e , e') → 
    dprod≅ (p d e) (λ l l' l'' → proj₁ (proj₂ (f (g l))) l' l'')}) ,
  (λ {(d , d') → proj₂ (proj₂ (f (g d))) d'})

plaw1 : ∀{X} → pbind (pη {X}) ≅ iden {pT X}
plaw1 {X} = ext (λ x → 
  let pr : prop (proj₁ x)
      pr p q = (proj₁ (proj₂ x)) p q

      pr' : prop (Σ (proj₁ x) (λ _ → ⊤))
      pr' p q = dprod≅ (pr (proj₁ p) (proj₁ q)) (λ _ _ _ → ⊤prop)
  in prod≅ (⇔ pr' pr proj₁ (λ y → y , _)) 
           (prod≅' (⇔p pr' pr proj₁ (λ y → y , _)) 
                   (⇔m pr' pr proj₁ (λ y → y , _) refl)))

plaw2 : ∀{X Y}{f : X → pT Y} → (pbind f) ∘ pη ≅ f
plaw2 {f = f} = ext (λ x → 
  let pr : prop (proj₁ (f x))
      pr p q = (proj₁ (proj₂ (f x))) p q

      pr' : prop (Σ ⊤ (λ _ → proj₁ (f x)))
      pr' p q = dprod≅ ⊤prop (λ _ y y' → pr y y')
  in prod≅ (⇔ pr' pr proj₂ (λ y → _ , y)) 
        (prod≅' (⇔p pr' pr proj₂ (λ y → _ , y)) 
                (⇔m pr' pr proj₂ ((λ y → _ , y)) refl)))

prf : {X Y : Set₁}(f : X → pT Y)(x : X) → prop (proj₁ (f x))
prf f x p q = (proj₁ (proj₂ (f x))) p q

plaw3 : ∀{X Y Z}{f : X → (pT Y)}{g : Y → (pT Z)} →
        pbind (comp (pbind g) f) ≅ comp (pbind g) (pbind f)
plaw3 {X}{Y}{Z}{f}{g} = ext (λ x → 
  let pr : prop (proj₁ x)
      pr p q = (proj₁ (proj₂ x)) p q

      pr' : prop (proj₁ (pbind (comp (pbind g) f) x))
      pr' p q = 
        dprod≅ (pr (proj₁ p) (proj₁ q)) 
               (λ d y y' → 
                 dprod≅ (prf f ((proj₂ (proj₂ x)) d) (proj₁ y) (proj₁ y')) 
                        (λ a z z' → 
                          prf g (proj₂ (proj₂ (f (proj₂ (proj₂ x) d))) a) z z'))

      pr'' : prop (proj₁ (comp (pbind g) (pbind f) x))
      pr'' p q = 
        dprod≅ 
          (dprod≅ (pr (proj₁ (proj₁ p)) (proj₁ (proj₁ q))) 
                  (λ d y y' → prf f (proj₂ (proj₂ x) d) y y')) 
          (λ a z z' → prf g (proj₂ (proj₂ (pbind f x)) a) z z')
  in prod≅ (⇔ pr' 
              pr''
              (λ {(d , d' , d'') → (d , d') , d''})
              (λ {((d , d') , d'') → d , d' , d''})) 
           (prod≅' (⇔p pr' 
                       pr'' 
                       (λ {(d , d' , d'') → (d , d') , d''}) 
                       (λ {((d , d') , d'') → d , d' , d''})) 
                   (⇔m pr' 
                       pr'' 
                       (λ {(d , d' , d'') → (d , d') , d''}) 
                       (λ {((d , d') , d'') → d , d' , d''}) 
                       refl)))

PredPar : Monad Sets
PredPar = record {
  T = pT; 
  η = pη;
  bind = pbind; 
  law1 = plaw1;
  law2 = plaw2;
  law3 = λ {_}{_}{_}{f}{g} → plaw3 {f = f} {g = g} }



{-

-- old approach using symmetric monoidal categories 

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

-}

{-
open import Data.Maybe
open import Data.Empty

Maybe→PredPart : ∀{X Y} → (X → Maybe Y) → X → pT Y
Maybe→PredPart f x with f x
Maybe→PredPart f x | just y = ⊤ , (λ _ → y)
Maybe→PredPart f x | nothing = ⊥ , ⊥-elim
-}


