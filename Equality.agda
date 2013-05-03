{-# OPTIONS --type-in-type #-}
module Equality where

open import Relation.Binary.HeterogeneousEquality
open import Data.Unit

record Σ' (A : Set)(B : A → Set) : Set where
    constructor _,,_
    field fst : A
          .snd : B fst
open Σ' public

postulate ext : ∀{A : Set}{B : A → Set}{f g : ∀ x → B x} → 
                (∀ x → f x ≅ g x) → f ≅ g

data Reveal_is_ {A : Set} (x : Hidden A) (y : A) : Set where
  [_] : (eq : reveal x ≅ y) → Reveal x is y

inspect : ∀ {A : Set} {B : A → Set}
          (f : (x : A) → B x) (x : A) → Reveal (hide f x) is (f x)
inspect f x = [ refl ]

fixtypes : ∀{A}{a a' a'' a''' : A}{p : a ≅ a'}{q : a'' ≅ a'''} →
           a ≅ a'' → a' ≅ a''' → p ≅ q
fixtypes refl refl = ≡-to-≅ (proof-irrelevance _ _)

record R (A : Set)(P : Set) : Set where
  constructor _!_
  field a : A
        .p : P

open R


lem' : ∀{A : Set}{B : Set}{a a' : A}.(b : B).(b' : B) → a ≅ a' → 
       a ! b ≅ a' ! b'
lem' b b' refl = refl

lem : ∀{A B} → (r r' : R A B) →  a r ≅ a r' → r ≅ r'
lem {A}{B} r r' q = lem' (p r) (p r') q

