{-# OPTIONS --type-in-type #-}
module Utilities where

open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality
open import Data.Unit
open import Data.Product

record Σ' (A : Set)(B : A → Set) : Set where
    constructor _,,_
    field fst : A
          .snd : B fst
open Σ' public


postulate ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ a → f a ≅ g a) → f ≅ g

postulate iext : {A : Set}{B B' : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
                 (∀ a → f {a} ≅ g {a}) → 
                 _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

data Reveal_is_ {A : Set} (x : Hidden A) (y : A) : Set where
  [_] : (eq : reveal x ≅ y) → Reveal x is y


cong₃ : {A : Set}
        {B : A → Set}
        {C : (a : A) → B a → Set}
        {D : (a : A)(b : B a) → C a b → Set}
        {a a' : A} → a ≅ a' → 
        {b : B a}{b' : B a'} → b ≅ b' → 
        {c : C a b}{c' : C a' b'} → c ≅ c' → 
        (f : (a : A)(b : B a)(c : C a b) → D a b c) → f a b c ≅ f a' b' c'
cong₃ refl refl refl f = refl

cong₄ : {A : Set}
        {B : A → Set}
        {C : (a : A) → B a → Set}
        {D : (a : A) → B a → Set}
        {E : Set}
        {a a' : A} → a ≅ a' → 
        {b : B a}{b' : B a'} → b ≅ b' → 
        {c : C a b}{c' : C a' b'} → c ≅ c' → 
        {d : D a b}{d' : D a' b'} → d ≅ d' → 
        (f : (a : A)(b : B a) → C a b → D a b → E) → f a b c d ≅ f a' b' c' d'
cong₄ refl refl refl refl f = refl

inspect : ∀ {A : Set} {B : A → Set}
          (f : (x : A) → B x) (x : A) → Reveal (hide f x) is (f x)
inspect f x = [ refl ]

fixtypes : {A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
           {p : a ≅ a'}{q : a'' ≅ a'''} → 
           a ≅ a'' → a' ≅ a''' → p ≅ q
fixtypes refl refl = ≡-to-≅ (proof-irrelevance _ _)

fixtypes' : {A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
            {p : a ≅ a'}{q : a'' ≅ a'''} →
            a ≅ a'' → p ≅ q
fixtypes' {p = p}{q = q} r = fixtypes r (trans (sym p) (trans r q))

fixtypes'' : ∀{A}{a a' a'' a''' : A}{p : a ≅ a'}{q : a'' ≅ a'''} →
            a' ≅ a''' → p ≅ q
fixtypes'' {p = p}{q = q} r = fixtypes (trans p (trans r (sym q))) r 

EqR : (A : Set) → Set
EqR A = Σ (Rel A _) (λ R → IsEquivalence R)

record Quotient (A : Set) (R : EqR A) : Set where
  open Σ R renaming (proj₁ to _~_)
  field Q : Set

  compat : {B : Set} → (A → B) → Set
  compat f = ∀{a b} → a ~ b → f a ≅ f b

  field abs : A → Q      
        lift : ∀{B}(f : A → B) → compat f → Q → B
        ax1 : (a b : A) → a ~ b → abs a ≅ abs b
        ax2 : (a b : A) → abs a ≅ abs b → a ~ b
        ax3 : ∀{B}(f : A → B)(p : compat f) → (a : A) → 
              (lift f p) (abs a) ≅ f a

postulate quot : (A : Set) (R : EqR A) → Quotient A R

compat₂ : ∀{A A' B}(R : EqR A)(R' : EqR A') → (A → A' → B) → Set
compat₂ R R' f = 
  let open Σ R renaming (proj₁ to _~_) 
      open Σ R' renaming (proj₁ to _≈_) 
  in ∀{a b a' b'} → a ~ a' → b ≈ b' → f a b ≅ f a' b'

lift₂ : ∀{A A' B R R'}(q : Quotient A R)(q' : Quotient A' R')(f : A → A' → B) → 
        compat₂ R R' f → Quotient.Q q → Quotient.Q q' → B
lift₂ {A}{A'}{B}{R}{R'} q q' f p = 
  let open Σ R renaming (proj₁ to _~_; proj₂ to e) 
      open Σ R' renaming (proj₁ to _≈_; proj₂ to e')
      open Quotient q 
      open Quotient q' renaming (Q to Q'; abs to abs'; lift to lift')
  
      g : A → Q' → B
      g a = lift' (f a) (p (IsEquivalence.refl e))

      fa≅fb : ∀{a b : A} → a ~ b → f a ≅ f b
      fa≅fb r = ext (λ a' → p r (IsEquivalence.refl e'))

      h : Q → Q' → B
--(λ x → lift' x (p (IsEquivalence.refl e)))
      h = lift g (λ {a b} r → {!cong₂ {_}{_}{_}{A' → B}{}!})

  in h


--lift' (lift f (λ {a₁ a₂} r → ext (λ a₃ → p r (IsEquivalence.refl e'))) a) (λ {a₁ a₂} r → {!p (IsEquivalence.refl e) r!}) a'



--postulate .irrelevant : {A : Set} → .A → A
