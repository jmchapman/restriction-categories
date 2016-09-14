{-# OPTIONS --type-in-type #-}
module Utilities where

open import Relation.Binary public
open import Relation.Binary.HeterogeneousEquality public
open ≅-Reasoning renaming (begin_ to proof_) public
open import Data.Unit hiding (decSetoid; preorder; setoid; _≤_) public 
open import Data.Product public
open import Data.Sum public hiding (map)
open import Function public
open import Data.Nat public hiding (_≟_; _≤?_; decTotalOrder)

postulate 
  ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} → 
        (∀ a → f a ≅ g a) → f ≅ g

postulate 
  iext : {A : Set}{B B' : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
         (∀ a → f {a} ≅ g {a}) → 
         _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

proof-irr : {A B : Set}{x : A}{y : B}(p q : x ≅ y) → p ≅ q
proof-irr refl refl = refl

cong₃ : {A B C D : Set}
        (f : A → B → C → D)
        {a a' : A} → a ≅ a' → 
        {b b' : B} → b ≅ b' → 
        {c c' : C} → c ≅ c' → 
        f a b c ≅ f a' b' c'
cong₃ f refl refl refl = refl

fixtypes : {A B C D : Set}{a : A}{b : B}{c : C}{d : D}
           {p : a ≅ b}{q : c ≅ d} → b ≅ d → p ≅ q
fixtypes {p = refl}{refl} refl = refl

fixtypes2 : {A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
      {p : a ≅ a'}{q : a'' ≅ a'''} → a ≅ a'' → p ≅ q
fixtypes2 {p = refl}{refl} refl = refl

EqR : (A : Set) → Set
EqR A = Σ (Rel A _) IsEquivalence

open IsEquivalence renaming (refl to irefl; sym to isym; trans to itrans)

record Quotient (A : Set)(R : EqR A) : Set where
  open Σ R renaming (proj₁ to _∼_)
  field Q   : Set
        abs : A → Q 

  compat : (B : Q → Set)(f : (a : A) → B (abs a)) → Set
  compat B f = ∀{a b} → a ∼ b → f a ≅ f b
     
  field sound    : compat _ abs
        lift     : (B : Q → Set)(f : (a : A) → B (abs a))
                   (p : compat B f) → (x : Q) → B x
        liftbeta : (B : Q → Set)(f : (a : A) → B (abs a))
                   (p : compat B f)(a : A) → 
                   lift B f p (abs a) ≅ f a

postulate quot : (A : Set)(R : EqR A) → Quotient A R



-- propositional/squash

Triv : (X : Set) → EqR X
Triv X = (\ _ _ → ⊤) ,
         record { refl = tt ; sym = \ _ → tt ; trans = \ _ _ → tt }

∥_∥ : Set → Set
∥ X ∥ = Quotient.Q $ quot X (Triv X) 

box : {X : Set} → X → ∥ X ∥
box {X} x = Quotient.abs (quot X (Triv X)) x 



map∥ : {X Y : Set}(f : X → Y) → ∥ X ∥ → ∥ Y ∥
map∥ {X}{Y} f x = lift (λ _ → ∥ Y ∥) (absY ∘ f) (λ _ → soundY _) x
  where open Quotient (quot X (Triv X))
        open Quotient (quot Y (Triv Y)) renaming (abs to absY;
                                                  lift to liftY;
                                                  sound to soundY)


isProp∥ : ∀ {X X'} → {x : ∥ X ∥}{x' : ∥ X' ∥} → X ≅ X' → x ≅ x'
isProp∥ {X}{_}{bx}{bx'} refl = 
  lift (λ q → q ≅ bx') 
       (λ x → lift (λ q → abs x ≅ q) 
                   (λ _ → sound _) 
                   (λ _ → fixtypes (sound _)) 
                   bx') 
       (λ _ → fixtypes refl) 
       bx 
       where open Quotient (quot X (Triv X))

module QuotientLib {A : Set}{R : EqR A}(q : Quotient A R) where

  open Quotient q

  abs-surj : ∀(q : Q) → ∥ (Σ A λ a → abs a ≅ q) ∥
  abs-surj q = lift (λ q₁ → ∥ (Σ A (λ a → abs a ≅ q₁)) ∥) 
                    (λ a → box (a , refl)) 
                    (λ {a}{b} p → 
                      isProp∥ (cong (Σ A) (ext (λ x → cong (λ p → abs x ≅ p) (sound p))))) 
                    q

  liftCong : (B B' : Q → Set)
              {f : (a : A) → B (abs a)}{g : (a : A) → B' (abs a)}
              {p : compat B f}{p' : compat B' g} → 
              (∀ a → f a ≅ g a) → ∀ x → lift B f p x ≅ lift B' g p' x
  liftCong B B' {f}{g}{p}{p'} r = 
    lift (λ z → lift B f p z ≅ lift B' g p' z) 
          (λ a → 
            proof
            lift B f p (abs a)
            ≅⟨ liftbeta B f p a ⟩
            f a
            ≅⟨ r a ⟩
            g a
            ≅⟨ sym (liftbeta B' g p' a) ⟩
            lift B' g p' (abs a)
            ∎) 
          (λ s → fixtypes2 (cong (lift B f p) (sound s))) 

  liftabs≅iden : {x : Q} → lift _ abs sound x ≅ x
  liftabs≅iden =
    lift (λ z → lift _ abs sound z ≅ z)
          (liftbeta _ abs sound) 
          (λ p → fixtypes (sound p)) 
          _

module Quotient₂Lib {A A' : Set}{R : EqR A}{R' : EqR A'}
                    (q : Quotient A R)(q' : Quotient A' R') where

  open QuotientLib
  open Σ R renaming (proj₁ to _∼_; proj₂ to e)
  open Σ R' renaming (proj₁ to _≈_; proj₂ to e')
  open Quotient q
  open Quotient q' renaming (Q to Q'; abs to abs'; lift to lift'; 
                             sound to sound'; liftbeta to liftbeta')

  compat₂ : (B : Q → Q' → Set)
            (f : (a : A)(a' : A') → B (abs a) (abs' a')) → Set 
  compat₂ B f = ∀{a b a' b'} → a ∼ a' → b ≈ b' → f a b ≅ f a' b'

  lift₂ : (B : Q → Q' → Set)
          (f : (a : A)(a' : A') → B (abs a) (abs' a')) 
          (p : compat₂ B f)(x : Q)(x' : Q') → B x x'
  lift₂ B f p = 
    let g : (a : A)(x' : Q') → B (abs a) x'
        g a = lift' (B (abs a)) (f a) (p (irefl e))
    in lift (λ x → (x' : Q') → B x x') g 
             (λ r → ext (liftCong q' _ _ (λ _ → p r (irefl e'))))
  
  liftbeta₂ : (B : Q → Q' → Set)
              (f : (a : A)(a' : A') → B (abs a) (abs' a'))
              (p : compat₂ B f)(a : A)(a' : A') →
              lift₂ B f p (abs a) (abs' a') ≅ f a a'
  liftbeta₂ B f p a a' = 
    proof
    lift₂ B f p (abs a) (abs' a')
    ≅⟨ cong (λ g → g (abs' a')) (liftbeta (λ x → (x' : Q') → B x x') _ _ _) ⟩
    lift' (B (abs a)) (f a) (p (irefl e)) (abs' a')
    ≅⟨ liftbeta' (B (abs a)) _ _ _ ⟩
    f a a'
    ∎

module Quotient₃Lib {A A' A'' : Set}{R : EqR A}{R' : EqR A'}
                    {R'' : EqR A''}(q : Quotient A R)
                    (q' : Quotient A' R')(q'' : Quotient A'' R'') where

  open QuotientLib
  open Quotient₂Lib
  open Σ R renaming (proj₁ to _∼_; proj₂ to e)
  open Σ R' renaming (proj₁ to _≈_; proj₂ to e')
  open Σ R'' renaming (proj₁ to _≋_; proj₂ to e'')
  open Quotient q
  open Quotient q' renaming (Q to Q'; abs to abs'; lift to lift'; 
                             sound to sound'; liftbeta to liftbeta')
  open Quotient q'' renaming (Q to Q''; abs to abs''; lift to lift''; 
                              sound to sound''; liftbeta to liftbeta'')

  compat₃ : (B : Q → Q' → Q'' → Set)
            (f : (a : A)(a' : A')(a'' : A'') → 
                 B (abs a) (abs' a') (abs'' a'')) → Set
  compat₃ B f = 
    ∀{a b c a' b' c'} → a ∼ a' → b ≈ b' → c ≋ c' → f a b c ≅ f a' b' c'

  lift₃ : (B : Q → Q' → Q'' → Set)
           (f : (a : A)(a' : A')(a'' : A'') → 
                B (abs a) (abs' a') (abs'' a'')) →
           compat₃ B f → (x : Q)(x' : Q')(x'' : Q'') → B x x' x''
  lift₃ B f p = 
    let g : (a : A)(x' : Q')(x'' : Q'') → B (abs a) x' x''
        g a = lift₂ q' q'' (B (abs a)) (f a) (p (irefl e))
    in lift (λ x → (x' : Q')(x'' : Q'') → B x x' x'') g 
             (λ r → ext (liftCong q' _ _ 
               (λ s → ext (liftCong q'' _ _ 
                                   (λ a → p r (irefl e') (irefl e''))))))

record Stream (X : Set) : Set where
  coinductive
  field hd : X
        tl : Stream X
open Stream public


smap : {X Y : Set} → (X → Y) → Stream X → Stream Y
hd (smap f xs) = f (hd xs)
tl (smap f xs) = smap f (tl xs)

repeat : {X : Set} → X → Stream X
hd (repeat x) = x
tl (repeat x) = repeat x

left : {X : Set} → Stream X → (ℕ → X)
left xs zero    = hd xs
left xs (suc n) = left (tl xs) n

right : {X : Set} → (ℕ → X) → Stream X
hd (right f) = f zero
tl (right f) = right (f ∘ suc)
