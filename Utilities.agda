
module Utilities where

open import Level hiding (lift) public
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality public
open ≅-Reasoning renaming (begin_ to proof_) public
open import Data.Unit hiding (decSetoid; preorder; setoid; _≤_) public 
open import Data.Product public
open import Function public

postulate 
  ext : ∀{i j}{A : Set i}{B B' : A → Set j}{f : ∀ a → B a}{g : ∀ a → B' a} → 
        (∀ a → f a ≅ g a) → f ≅ g

postulate 
  iext : ∀{i j}{A : Set i}{B B' : A → Set j}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
         (∀ a → f {a} ≅ g {a}) → 
         _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

proof-irr : ∀{i}{A B : Set i}{x : A}{y : B}(p q : x ≅ y) → p ≅ q
proof-irr refl refl = refl

cong₃ : ∀{i j k l}
        {A : Set i}{B : Set j}
        {C : Set k}{D : Set l}
        (f : A → B → C → D)
        {a a' : A} → a ≅ a' → 
        {b b' : B} → b ≅ b' → 
        {c c' : C} → c ≅ c' → 
        f a b c ≅ f a' b' c'
cong₃ f refl refl refl = refl

fixtypes : ∀{i}{A B C D : Set i}{a : A}{b : B}{c : C}{d : D}
           {p : a ≅ b}{q : c ≅ d} → b ≅ d → p ≅ q
fixtypes {p = refl}{refl} refl = refl

fixtypes2 : ∀{i}{A B C D : Set i}{a : A}{b : B}{c : C}{d : D}
            {p : a ≅ b}{q : c ≅ d} → a ≅ c → p ≅ q
fixtypes2 {p = refl}{refl} refl = refl

EqR : ∀{i}(A : Set i) → Set (suc i)
EqR A = Σ (Rel A _) IsEquivalence

open IsEquivalence renaming (refl to irefl; sym to isym; trans to itrans)

record Quotient {i j}(A : Set i)(R : EqR A) : Set (suc (i ⊔ j)) where
  open Σ R renaming (proj₁ to _∼_)
  field Q   : Set j
        abs : A → Q 

  compat : (B : Q → Set j)(f : (a : A) → B (abs a)) → Set (i ⊔ j)
  compat B f = ∀{a b} → a ∼ b → f a ≅ f b
     
  field sound    : compat _ abs
        lift     : (B : Q → Set j)(f : (a : A) → B (abs a))
                   (p : compat B f) → (x : Q) → B x
        liftbeta : (B : Q → Set j)(f : (a : A) → B (abs a))
                   (p : compat B f)(a : A) → 
                   lift B f p (abs a) ≅ f a

postulate quot : ∀{i j}(A : Set i)(R : EqR A) → Quotient {i}{j} A R

module QuotientLib {i j}{A : Set i}{R : EqR A}(q : Quotient {i}{j} A R) where

  open Quotient q

  liftCong : (B B' : Q → Set j)
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

module Quotient₂Lib {i j}{A A' : Set i}{R : EqR A}{R' : EqR A'}
                    (q : Quotient {i}{j} A R)(q' : Quotient {i}{j} A' R') where

  open QuotientLib
  open Σ R renaming (proj₁ to _∼_; proj₂ to e)
  open Σ R' renaming (proj₁ to _≈_; proj₂ to e')
  open Quotient q
  open Quotient q' renaming (Q to Q'; abs to abs'; lift to lift'; 
                             sound to sound'; liftbeta to liftbeta')

  compat₂ : (B : Q → Q' → Set j)
            (f : (a : A)(a' : A') → B (abs a) (abs' a')) → Set (i ⊔ j)
  compat₂ B f = ∀{a b a' b'} → a ∼ a' → b ≈ b' → f a b ≅ f a' b'

  lift₂ : (B : Q → Q' → Set j)
          (f : (a : A)(a' : A') → B (abs a) (abs' a')) 
          (p : compat₂ B f)(x : Q)(x' : Q') → B x x'
  lift₂ B f p = 
    let g : (a : A)(x' : Q') → B (abs a) x'
        g a = lift' (B (abs a)) (f a) (p (irefl e))
    in lift (λ x → (x' : Q') → B x x') g 
             (λ r → ext (liftCong q' _ _ (λ _ → p r (irefl e'))))
  
  liftbeta₂ : (B : Q → Q' → Set j)
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

module Quotient₃Lib {i j}{A A' A'' : Set i}{R : EqR A}{R' : EqR A'}
                    {R'' : EqR A''}(q : Quotient {i}{j} A R)
                    (q' : Quotient {i}{j} A' R')(q'' : Quotient {i}{j} A'' R'') where

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

  compat₃ : (B : Q → Q' → Q'' → Set j)
            (f : (a : A)(a' : A')(a'' : A'') → 
                 B (abs a) (abs' a') (abs'' a'')) → Set (i ⊔ j)
  compat₃ B f = 
    ∀{a b c a' b' c'} → a ∼ a' → b ≈ b' → c ≋ c' → f a b c ≅ f a' b' c'

  lift₃ : (B : Q → Q' → Q'' → Set j)
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


