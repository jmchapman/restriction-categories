
module Monads.Delay.Products where

open import RestrictionDelay
open import Coinduction
open import Data.Product
open import Categories
open import Monads.Kleisli
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import RestrictionCat
open import Monads.Delay
open Cat (Kl DelayM)
open RestCat DelayR
open import RestrictionProducts DelayR
open import Totals DelayR
open Tot
open import Utilities

{-
-- Restriction product

-- Projections

dp₁ : ∀{X Y} → Tot (X × Y) X
dp₁ = record { 
  hom = λ { (x , y) → now x }; 
  tot = refl }

dp₂ : ∀{X Y} → Tot (X × Y) Y
dp₂ = record { 
  hom = λ { (x , y) → now y }; 
  tot = refl }

-- Pairing

d⟨_,_⟩-aux : {X Y : Set} → Delay X → Delay Y → Delay (X × Y)
d⟨ now x , now y ⟩-aux = now (x , y)
d⟨ now x , later dy ⟩-aux = later (♯ d⟨ now x , ♭ dy ⟩-aux)
d⟨ later dx , now y ⟩-aux = later (♯ d⟨ ♭ dx , now y ⟩-aux)
d⟨ later dx , later dy ⟩-aux = later (♯ d⟨ ♭ dx , ♭ dy ⟩-aux)

d⟨_,_⟩ : {X Y Z : Set} → (Z → Delay X) → (Z → Delay Y) → Z → Delay (X × Y)
d⟨ f , g ⟩ z = d⟨ f z , g z ⟩-aux 

-- First triangle commutes

dtr1-aux' : ∀{X Y}{dx : Delay X}{dy : Delay Y} →
            dbind (hom dp₁) d⟨ dx , dy ⟩-aux ≈ dcomp dy dx 
dtr1-aux' {X}{Y}{now x}{now y} = ↓≈ now↓ now↓
dtr1-aux' {X}{Y}{later dx}{now y} = later≈ (♯ dtr1-aux' {_}{_}{♭ dx})
dtr1-aux' {X}{Y}{now x}{later dy} = later≈ (♯ dtr1-aux' {_}{_}{_}{♭ dy})
dtr1-aux' {X}{Y}{later dx}{later dy} = later≈ (♯ dtr1-aux' {_}{_}{♭ dx})

dtr1-aux : ∀{X Y}{dx : Delay X}{dy : Delay Y} →
           dbind (hom dp₁) d⟨ dx , dy ⟩-aux ≈ dbind (λ _ → dx) dy
dtr1-aux {X}{Y}{dx}{dy} = trans≈ (dtr1-aux' {_}{_}{dx}) (dcomp≈dbind {_}{_}{dy})

dtr1 : ∀{X Y Z}{f : Z → Delay X}{g : Z → Delay Y}(z : Z) → 
       comp (hom dp₁) d⟨ f , g ⟩ z ≅ comp f (drest g) z
dtr1 {X}{Y}{Z}{f}{g} z = 
  proof
  comp (hom dp₁) d⟨ f , g ⟩ z
  ≅⟨ quotient (dtr1-aux {dx = f z}{dy = g z}) ⟩
  dbind (λ _ → f z) (g z)
  ≅⟨ compdrest {f = f} {g = g} z ⟩
  dbind f (dbind (λ a → now z) (g z))
  ≅⟨ cong (dbind f) (sym (drest≅ z g)) ⟩ 
  dbind f (drest g z)
  ∎

-- Second triangle commutes

dtr2-aux' : ∀{X Y}{dx : Delay X}{dy : Delay Y} →
            dbind (hom dp₂) d⟨ dx , dy ⟩-aux ≈ dcomp dx dy 
dtr2-aux' {X}{Y}{now x}{now y} = ↓≈ now↓ now↓
dtr2-aux' {X}{Y}{later dx}{now y} = later≈ (♯ dtr2-aux' {_}{_}{♭ dx})
dtr2-aux' {X}{Y}{now x}{later dy} = later≈ (♯ dtr2-aux' {_}{_}{now x}{♭ dy})
dtr2-aux' {X}{Y}{later dx}{later dy} = later≈ (♯ dtr2-aux' {_}{_}{♭ dx})

dtr2-aux : ∀{X Y}{dx : Delay X}{dy : Delay Y} →
           dbind (hom dp₂) d⟨ dx , dy ⟩-aux ≈ dbind (λ _ → dy) dx
dtr2-aux {X}{Y}{dx} = trans≈ (dtr2-aux' {_}{_}{dx}) (dcomp≈dbind {_}{_}{dx})

dtr2 : ∀{X Y Z}{f : Z → Delay X}{g : Z → Delay Y}(z : Z) → 
       comp (hom dp₂) d⟨ f , g ⟩ z ≅ comp g (drest f) z
dtr2 {X}{Y}{Z}{f}{g} z = 
  proof
  comp (hom dp₂) d⟨ f , g ⟩ z
  ≅⟨ quotient (dtr2-aux {dx = f z} {dy = g z}) ⟩
  dbind (λ _ → g z) (f z)
  ≅⟨ compdrest {f = g} {g = f} z ⟩
  dbind g (dbind (λ a → now z) (f z))
  ≅⟨ cong (dbind g) (sym (drest≅ z f)) ⟩ 
  dbind g (drest f z)
  ∎

-- Universal property

uniq-aux' : {X Y : Set}{x : X}{y : Y}(dxy : Delay (X × Y)) →
            dbind (hom dp₁) dxy ↓ x → dbind (hom dp₂) dxy ↓ y → dxy ↓ (x , y)
uniq-aux' {X} {Y} {x} {y} (now (.x , .y)) now↓ now↓ = now↓
uniq-aux' (later dxy) (later↓ p) (later↓ q) = later↓ (uniq-aux' (♭ dxy) p q)

uniq-aux : {X Y : Set}(dxy dxy' : Delay (X × Y)) →
           dbind (hom dp₁) dxy ≈ dbind (hom dp₁) dxy' → 
           dbind (hom dp₂) dxy ≈ dbind (hom dp₂) dxy' → dxy ≈ dxy'
uniq-aux (now (x , y)) (now (.x , .y)) (↓≈ now↓ now↓) (↓≈ now↓ now↓) = 
  ↓≈ now↓ now↓
uniq-aux (now (x , y)) (later dxy) (↓≈ now↓ (later↓ p)) (↓≈ now↓ (later↓ q)) = 
  ↓≈ now↓ (later↓ (uniq-aux' (♭ dxy) p q))
uniq-aux (later dxy) (now (x , y)) (↓≈ (later↓ p) now↓) (↓≈ (later↓ q) now↓) = 
  ↓≈ (later↓ (uniq-aux' (♭ dxy) p q)) now↓
uniq-aux (later dxy) 
         (later dxy') 
         (↓≈ (later↓ p) (later↓ p')) 
         (↓≈ (later↓ q) (later↓ q')) = 
  later≈ (♯ (uniq-aux (♭ dxy) (♭ dxy') (↓≈ p p') (↓≈ q q')))
uniq-aux (later dxy) (later dxy') (↓≈ (later↓ p) (later↓ p')) (later≈ q) = 
  later≈ (♯ (uniq-aux (♭ dxy) (♭ dxy') (↓≈ p p') (♭ q)))
uniq-aux (later dxy) (later dxy') (later≈ p) (↓≈ (later↓ q) (later↓ q')) = 
  later≈ (♯ (uniq-aux (♭ dxy) (♭ dxy') (♭ p) (↓≈ q q')))
uniq-aux (later dxy) (later dxy') (later≈ p) (later≈ q) = 
  later≈ (♯ (uniq-aux (♭ dxy) (♭ dxy') (♭ p) (♭ q)))

uniq : ∀{X Y Z}{f : Z → Delay X}{g : Z → Delay Y}(u : Z → Delay (X × Y)) → 
       comp (hom dp₁) u ≅ comp f (rest g) → 
       comp (hom dp₂) u ≅ comp g (rest f) → (z : Z) → u z ≅ d⟨ f , g ⟩ z
uniq {f = f}{g = g} u p q z = 
  quotient (uniq-aux (u z) 
                     (d⟨ f , g ⟩ z) 
                     (subst (λ h → h z ≈ dbind (hom dp₁) (d⟨ f , g ⟩ z)) 
                            (sym p) 
                            (subst (λ x → comp f (rest g) z ≈ x) 
                                   (sym (dtr1 {f = f}{g = g} z)) 
                                   refl≈)) 
                     (subst (λ h → h z ≈ dbind (hom dp₂) (d⟨ f , g ⟩ z)) 
                            (sym q) 
                            (subst (λ x → comp g (rest f) z ≈ x) 
                                   (sym (dtr2 {f = f}{g = g} z)) 
                                   refl≈)))

DelayProd : (X Y : Set) → RestProd X Y
DelayProd X Y = record {
  W = X × Y;
  p₁ = dp₁;
  p₂ = dp₂;
  ⟨_,_⟩ = d⟨_,_⟩;
  tr1 = λ {Z}{f}{g} → ext (dtr1 {f = f} {g = g});
  tr2 = λ {Z}{f}{g} → ext (dtr2 {f = f} {g = g});
  uniq = λ {Z}{f}{g} u p q → ext (uniq {f = f} {g = g} u p q) }

-}

