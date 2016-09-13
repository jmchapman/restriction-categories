module AComega where

open import Data.Nat hiding (_+_) public
open import Utilities
open IsEquivalence renaming (refl to irefl; sym to isym; trans to itrans)


Triv : (X : Set) → EqR X
Triv X = (\ _ _ → ⊤) ,
         record { refl = tt ; sym = \ _ → tt ; trans = \ _ _ → tt }

∥_∥ : Set → Set
∥ X ∥ = Quotient.Q $ quot X (Triv X) 

map∥ : {X Y : Set}(f : X → Y) → ∥ X ∥ → ∥ Y ∥
map∥ {X}{Y} f x = lift (λ _ → ∥ Y ∥) (absY ∘ f) (λ _ → soundY _) x
  where open Quotient (quot X (Triv X))
        open Quotient (quot Y (Triv Y)) renaming (abs to absY;
                                                  lift to liftY;
                                                  sound to soundY)

record Stream (X : Set) : Set where
  coinductive
  field hd : X
        tl : Stream X
open Stream


left : {X : Set} → Stream X → (ℕ → X)
left xs zero    = hd xs
left xs (suc n) = left (tl xs) n

right : {X : Set} → (ℕ → X) → Stream X
hd (right f) = f zero
tl (right f) = right (f ∘ suc)

-- Axiom of countable choice.

ACω : Set₁
ACω = 
  {X : Set}(P : ℕ → X → Set)(r : (n : ℕ) → ∥ Σ X (λ x → P n x) ∥) → 
  ∥ Σ (ℕ → X) (λ f → (n : ℕ) → P n (f n)) ∥

postulate 
  acω : ACω

ACω₂ : Set₁
ACω₂ = (P : ℕ → Set)(r : (n : ℕ) → ∥ P n ∥) → ∥ ((n : ℕ) → P n) ∥

ACco : Set₁
ACco = {X : Set} → Stream ∥ X ∥ → ∥ Stream X ∥ 

ACω₂→ACco : ACω₂ → ACco
ACω₂→ACco p xs = map∥ right (p _ (left xs))

ACω→ACω₂ : ACω → ACω₂
ACω→ACω₂ acω P r = map∥ proj₂ s
  where
    s : ∥ Σ (ℕ → ⊤) (λ f → (n : ℕ) → P n) ∥
    s = acω _ (λ n → map∥ (λ p → _ , p) (r n))

ACω₂→ACω : ACω₂ → ACω
ACω₂→ACω acω₂ P r = map∥ (λ f → proj₁ ∘ f , proj₂ ∘ f) (acω₂ _ r)

acco : ACco
acco = ACω₂→ACco (ACω→ACω₂ acω)
