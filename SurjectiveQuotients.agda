{-# OPTIONS --type-in-type #-}
module SurjectiveQuotients where

open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product
open import Data.Bool
open import Data.Sum

EqR : (A : Set) → Set
EqR A = Σ (Rel A _) (λ R → IsEquivalence R)

record Quotient (A : Set) (R : EqR A) : Set where
  open Σ R renaming (proj₁ to _~_)
  field Q : Set
        abs : A → Q
        rep : Q → A
        ax1 : (a b : A) → a ~ b → abs a ≡ abs b
        ax2 : (q : Q) → abs (rep q) ≡ q
        ax3 : (a : A) → rep (abs a) ~ a

postulate quot : (A : Set) (R : EqR A) → Quotient A R

module Classical (P : Set) where

  _R_ : Bool → Bool → Set
  x R y = x ≡ y ⊎ P
  
  reflR : ∀{x} → x R x
  reflR = inj₁ refl
  
  symR : ∀{x y} → x R y → y R x
  symR (inj₁ refl) = inj₁ refl
  symR (inj₂ p) = inj₂ p
  
  transR : ∀{x y z} → x R y → y R z → x R z
  transR (inj₁ refl) (inj₁ refl) = inj₁ refl
  transR (inj₁ refl) (inj₂ p) = inj₂ p
  transR (inj₂ p) q = inj₂ p
  
  EqR-R : EqR Bool
  EqR-R = _R_ , record { refl = reflR; sym = symR; trans = transR }
  
  quotR : Quotient Bool EqR-R
  quotR = quot Bool EqR-R
  
  open Quotient quotR
  
  lemma : rep (abs true) ≡ rep (abs false) → P
  lemma q with 
    transR (symR (ax3 true)) 
           (transR (subst (_R_ (rep (abs true))) q reflR) (ax3 false))
  lemma q | inj₁ ()
  lemma q | inj₂ p = p
  
  lemma2 : P → rep (abs true) ≡ rep (abs false)
  lemma2 p = cong rep (ax1 true false (inj₂ p))
  
  P⊎¬P : P ⊎ ¬ P
  P⊎¬P with rep (abs true) ≟ rep (abs false)
  P⊎¬P | yes q = inj₁ (lemma q)
  P⊎¬P | no ¬q = inj₂ (λ p → ¬q (lemma2 p))