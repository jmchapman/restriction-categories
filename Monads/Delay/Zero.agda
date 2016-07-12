{-# OPTIONS --type-in-type #-}
module Monads.Delay.Zero where

open import Relation.Binary.HeterogeneousEquality
open import Monads.Delay
open import Coinduction
open import Restriction.Cat
open import Categories
open import Monads.Kleisli
open Cat (Kl DelayM)
open import Restriction.Delay
open RestCat DelayR
open import Utilities
open import Relation.Binary
open IsEquivalence renaming (refl to irefl; sym to isym; trans to itrans)

-- Restriction zeros

-- zero maps every element in the domain to the non-terminating computation

zero : {A B : Set} → A → Delay B
zero a = later (♯ zero a)

qzero : {A B : Set} → A → QDelay B
qzero a = abs (zero a)

dbindzero : ∀{A B C}{f : B → Delay C}{a : A} → dbind f (zero a) ≈ zero a
dbindzero {a = a} = later≈ (♯ dbindzero {a = a})

-- The two properties of a restriction zero. Here are called qf0g=0 and qrest0=0

df0g=0' : ∀{A B C D}(g : C → Delay D)(b : B)(a : A) → 
          dbind g (zero b) ≈ zero a
df0g=0' g b a = later≈ (♯ df0g=0' g b a)

df0g=0 : ∀{A B C D}(g : C → Delay D)(f : A → Delay B)(a : A) → 
         dbind g (zero (f a)) ≈ zero a
df0g=0 g f a = df0g=0' g (f a) a

.qf0g=0' : ∀{A B C D}(g : C → QDelay D)(b : B)(a : A) → 
           comp g qzero b ≅ qzero {B = D} a
qf0g=0' {A}{B}{C}{D} g b a = 
  proof
  qbind g (abs (zero b)) 
  ≅⟨ qbindabs ⟩
  lift-map {Z = λ _ → QDelay D}
           (λ h → abs (dbind h (zero b))) 
           (λ r → compat-abs-dbind {_}{_}{_}{_}{_}{zero {B = C} b} r (irefl (proj₂ ≈EqR)))
           (~→map~ g)
  ≅⟨ lift-map
       {Z =
        λ h →
          lift-map {Z = λ _ → QDelay D} (λ l → abs (dbind l (zero b)))
          (λ r →
             compat-abs-dbind {_} {_} {_} {_} {_} {zero {B = C} b} r
             (irefl (proj₂ ≈EqR)))
          h
          ≅ abs (zero a)}
       (λ h → 
         proof
         lift-map {Z = λ _ → QDelay D} (λ l → abs (dbind l (zero b)))
         (λ r →
            compat-abs-dbind {_} {_} {_} {_} {_} {zero {B = C} b} r
            (irefl (proj₂ ≈EqR)))
         (abs-map h)
         ≅⟨ ax3-map (λ l → abs (dbind l (zero b))) 
                    (λ r → compat-abs-dbind {_} {_} {_} {_} {_} {zero {B = C} b} r (irefl (proj₂ ≈EqR))) 
                    h ⟩
         abs (dbind h (zero b))
         ≅⟨ ax1 _ _ (df0g=0' h b a) ⟩
         abs (zero a)
         ∎) 
       (λ r → fixtypes' (cong (lift-map (λ l → abs (dbind l (zero b)))
                                        (λ s → compat-abs-dbind {_} {_} {_} {_} {_} {zero {B = C} b} s (irefl (proj₂ ≈EqR))))
                              (ax1-map _ _ r))) 
       (~→map~ g) ⟩
  abs (zero a)
  ∎

.qf0g=0 : ∀{A B C D}(g : C → QDelay D)(f : A → QDelay B)(a : A) → 
          comp g qzero (f a) ≅ qzero {B = D} a
qf0g=0 g f a = qf0g=0' g (f a) a

.qrest0=0 : ∀{A B}(a : A) → qrest (qzero {B = B}) a ≅ qzero {B = A} a
qrest0=0 {A}{B} a = 
  proof
  qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (a , y))) (abs (zero a)))
  ≅⟨ cong (λ l → l (abs (zero a))) (sym qlaw3) ⟩
  qbind (qbind (abs ∘ now ∘ proj₁) ∘ abs ∘ now ∘ (λ y → a , y)) (abs (zero a))
  ≅⟨ cong (λ g → qbind g (abs (zero a))) (ext (λ _ → qbindabsabs)) ⟩
  qbind (λ y → abs (dbind (now ∘ proj₁) (now (a , y)))) (abs (zero a))
  ≡⟨⟩
  qbind (λ _ → abs (now a)) (abs (zero a))
  ≅⟨ qbindabsabs ⟩
  abs (dbind (λ _ → now a) (zero a))
  ≅⟨ ax1 _ _ dbindzero ⟩
  abs (zero a)
  ∎
