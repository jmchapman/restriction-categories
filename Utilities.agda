{-# OPTIONS --type-in-type #-}
module Utilities where

open import Relation.Binary.HeterogeneousEquality
open import Data.Unit

record Σ' (A : Set)(B : A → Set) : Set where
    constructor _,,_
    field fst : A
          .snd : B fst
open Σ' public


postulate ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ a → f a ≅ g a) → f ≅ g

postulate iext : {A : Set}{B B' : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
                 (∀ a → f {a} ≅ g {a}) → 
                 _≅_ {_}{ {a : A} → B a} f {_} { {a : A} → B' a} g

--data Reveal_is_ {A : Set} (x : Hidden A) (y : A) : Set where
--  [_] : (eq : reveal x ≅ y) → Reveal x is y


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

--inspect : ∀ {A : Set} {B : A → Set}
--          (f : (x : A) → B x) (x : A) → Reveal (hide f x) is (f x)
--inspect f x = [ refl ]

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

record EqR (A : Set) : Set where
  field _~_    : A → A → Set
        ~refl  : ∀{a} → a ~ a
        ~sym   : ∀{a a'} → a ~ a' → a' ~ a
        ~trans : ∀{a a' a''} → a ~ a' → a' ~ a'' → a ~ a''

record Quotient (A : Set) (EQ : EqR A) : Set where
  open EqR EQ
  field Q : Set
        abs : A → Q
        rep : Q → A
        ax1 : (a b : A) → a ~ b → abs a ≅ abs b
        ax2 : (q : Q) → abs (rep q) ≅ q
        ax3 : (a : A) → rep (abs a) ~ a

postulate quot : (A : Set) (EQ : EqR A) → Quotient A EQ

postulate .irrelevant : {A : Set} → .A → A
