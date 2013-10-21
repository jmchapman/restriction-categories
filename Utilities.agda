
module Utilities where

open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality
open import Data.Unit
open import Level
open import Data.Product

record Σ' {a b}(A : Set a)(B : A → Set b) : Set (a ⊔ b) where
    constructor _,,_
    field fst : A
          .snd : B fst
open Σ' public

postulate ext : ∀{a b}{A : Set a}{B B' : A → Set b}{f : ∀ a → B a}
                {g : ∀ a → B' a} → (∀ a → f a ≅ g a) → f ≅ g

postulate iext : ∀{a b}{A : Set a}{B B' : A → Set b}{f : ∀ {a} → B a}
                 {g : ∀{a} → B' a} → (∀ a → f {a} ≅ g {a}) → 
                 _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

data Reveal_is_ {A : Set} (x : Hidden A) (y : A) : Set where
  [_] : (eq : reveal x ≅ y) → Reveal x is y

cong₃ : ∀{a b c d}
        {A : Set a}
        {B : A → Set b}
        {C : (a : A) → B a → Set c}
        {D : (a : A)(b : B a) → C a b → Set d}
        {x x' : A} → x ≅ x' → 
        {y : B x}{y' : B x'} → y ≅ y' → 
        {z : C x y}{z' : C x' y'} → z ≅ z' → 
        (f : (x : A)(y : B x)(z : C x y) → D x y z) → f x y z ≅ f x' y' z'
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

fixtypes : ∀{i}{A A' A'' A''' : Set i}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
           {p : a ≅ a'}{q : a'' ≅ a'''} → 
           a ≅ a'' → a' ≅ a''' → p ≅ q
fixtypes refl refl = ≡-to-≅ (proof-irrelevance _ _)

fixtypes' : ∀{i}{A A' A'' A''' : Set i}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
            {p : a ≅ a'}{q : a'' ≅ a'''} →
            a ≅ a'' → p ≅ q
fixtypes' {p = p}{q = q} r = fixtypes r (trans (sym p) (trans r q))

fixtypes'' : ∀{i}{A : Set i}{a a' a'' a''' : A}{p : a ≅ a'}{q : a'' ≅ a'''} →
            a' ≅ a''' → p ≅ q
fixtypes'' {p = p}{q = q} r = fixtypes (trans p (trans r (sym q))) r 

postulate irrelevant : ∀{i}{A : Set i} → .A → A

EqR : ∀{a}(A : Set a) → Set (suc a)
EqR {a} A = Σ (Rel A a) (λ R → IsEquivalence R)

record Quotient {a : Level} (A : Set a) (R : EqR A) : Set (suc a) where
  open Σ R renaming (proj₁ to _~_)
  field Q : Set a
        abs : A → Q
        rep : Q → A
        ax1 : (a b : A) → a ~ b → abs a ≅ abs b
        ax2 : (q : Q) → abs (rep q) ≅ q
        ax3 : (a : A) → rep (abs a) ~ a

postulate quot : ∀{a}(A : Set a) (R : EqR A) → Quotient A R

