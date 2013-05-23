module RestrictionDelay where

open import Coinduction
open import Categories
open import Monads
open import Functors
open import Kleisli
open import Sets
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open import Data.Product hiding (map)
open ≅-Reasoning renaming (begin_ to proof_)
open import RestrictionCat
open import DelayMonad

map = Fun.HMap (TFun DelayM)

str : ∀{X Y} → X × Delay Y → Delay (X × Y)
str (x , dy) = map (λ y → (x , y)) dy

--str : ∀{X Y} → Delay X × Delay Y → Delay (X × Y)

drest : ∀{X Y} → (X → Delay Y) → X → Delay X
drest f x = map proj₁ (str (x , f x))

open Cat (Kl DelayM)

data _R_ {X : Set} : Delay X → Delay X → Set where
  nowR : ∀{x} → now x R now x
  later2 : ∀{dx dx'} → ∞ (♭ dx R ♭ dx') → later (♯ (later dx)) R later dx'

lemma : ∀{X}(dx : Delay X) → dbind (λ _ → dx) dx R dx
lemma (now x) = nowR
lemma (later x) = {!later!}

dR1 : ∀{X Y}{f : X → Delay Y}(x : X) → (dbind f ∘ (drest f)) x ≅ f x
dR1 {f = f} x = 
  let open Monad DelayM 
  in  proof
      dbind f (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x)))
      ≅⟨ cong (λ f' → dbind f (f' (f x)))
              (sym (law3 {f = λ y → now (x , y)} {g = now ∘ proj₁})) ⟩
      dbind f (dbind (λ _ → now x) (f x))
      ≅⟨ cong (λ f' → f' (f x)) (sym (law3 {f = λ _ → now x} {g = f})) ⟩
      dbind (λ _ → f x) (f x)
      ≅⟨ {!!} ⟩
      f x 
      ∎

{-
DelayR : RestCat
DelayR = record { 
  cat  = Kl DelayM; 
  rest = drest; 
  R1   = {!Monad.law3 DelayM!}; 
  R2   = {!!}; 
  R3   = {!!}; 
  R4   = {!!} }
-}

