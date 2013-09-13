{-# OPTIONS --type-in-type #-}

module Quotients where

open import Data.Product
open import Relation.Binary.HeterogeneousEquality

record EqR (A : Set) : Set where
  field _~_    : A → A → Set
        ~refl  : ∀{a} → a ~ a
        ~sym   : ∀{a a'} → a ~ a' → a' ~ a
        ~trans : ∀{a a' a''} → a ~ a' → a' ~ a'' → a ~ a''

record Quotient (A : Set)(EQ : EqR A) : Set where
  open EqR EQ
  field Q : Set
        abs : A → Q
        rep : Q → A
        ax1 : (a b : A) → a ~ b → abs a ≅ abs b
        ax2 : (q : Q) → abs (rep q) ≅ q
        ax3 : (a : A) → rep (abs a) ~ a

--[_] : ∀{A EQ} → Quotient A EQ → Set
--[ q ] = Quotient.Q q

postulate quot : (A : Set)(EQ : EqR A) → Quotient A EQ
