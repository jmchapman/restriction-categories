{-# OPTIONS --type-in-type #-}
module RestrictionDelay where

open import Coinduction
open import Categories
open import Monads
open import Functors
open import Monads.Kleisli
open import Sets
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open import Data.Product hiding (map)
open ≅-Reasoning renaming (begin_ to proof_)
open import RestrictionCat
open import Monads.Delay

drest : ∀{X Y} → (X → Delay Y) → X → Delay X
drest f x = map proj₁ (str (x , f x))

open Cat (Kl DelayM)

dbind↓' : ∀{X}{dx dz : Delay X}{y : X} → dbind (λ _ → dx) dx ∼ dz → dz ↓ y → dx ↓ y
dbind↓' {X} {now .y} now∼ (now↓ {y}) = now↓
dbind↓' {X} {later x} {now z} () q
dbind↓' {X} {later dx} (later∼ p) (later↓' q now↓) with trans∼ (sym∼ (dbindlater (λ _ → dx) (♭ dx))) (trans∼ (♭ p) (sym∼ q))
dbind↓' {X} {later dx} (later∼ p) (later↓' q now↓) | ()
dbind↓' {X} {later dx} (later∼ p) (later↓' q (later↓' r r')) with trans∼ (sym∼ (dbindlater (λ _ → dx) (♭ dx))) (trans∼ (♭ p) (sym∼ q))
dbind↓' {X} {later dx} (later∼ p) (later↓' q (later↓' r r')) | later∼ a = later↓ (dbind↓' (trans∼ (♭ a) (sym∼ r)) r')

dbind↓ : ∀{X}{dx : Delay X}{y : X} → dbind (λ _ → dx) dx ↓ y → dx ↓ y
dbind↓ = dbind↓' refl∼

lemma' : ∀{X}{dx dz : Delay X} → dbind (λ _ → dx) dx ≈ dz → dx ≈ dz
lemma' {X} {now x} (↓≈ p q) = ↓≈ p q
lemma' {X} {later dx} {dz} (↓≈ (later↓' {dz = dy} p p') q) = 
               ↓≈
                (later↓
                 (dbind↓
                  (≈↓
                   (stable≈ (trans∼ p (dbindlater (λ _ → dx) (♭ dx))) 
                            (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem))
                            refl∼)
                   p')))
                q

lemma' {X} {later dx} {later dz} (later≈ p) = later≈ (♯ lemma' (trans≈ (trans≈ (trans≈ (laterlem {_} {dbind (λ _ → ♭ dx) (♭ dx)}) (later≈ (♯ refl≈))) (sym≈ (∼→≈ (dbindlater _ (♭ dx))))) (♭ p)))

lemma : ∀{X}{dx : Delay X} → dx ≈ dbind (λ _ → dx) dx
lemma = lemma' refl≈


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
      ≅⟨ quotient (sym≈ (lemma {_}{f x})) ⟩
      f x 
      ∎


DelayR : RestCat
DelayR = record { 
  cat  = Kl DelayM; 
  rest = drest; 
  R1   = λ {_}{_}{f} → ext (dR1 {f = f});
  R2   = {!!}; 
  R3   = {!!}; 
  R4   = {!!} }


