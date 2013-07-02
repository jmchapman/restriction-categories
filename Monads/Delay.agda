{-# OPTIONS --type-in-type #-}
module Monads.Delay where

open import Coinduction
open import Monads
open import Sets
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open import Functors
open import Data.Product hiding (map)

data Delay (X : Set) : Set where
  now : X → Delay X
  later : ∞ (Delay X) → Delay X

-- strong bisimilarity

data _∼_ {X : Set} : Delay X → Delay X → Set where
  now∼ : ∀{x} → now x ∼ now x
  later∼ : ∀{dy dy'} → ∞ (♭ dy ∼ ♭ dy') → later dy ∼ later dy'

refl∼ : ∀{X}{dx : Delay X} → dx ∼ dx
refl∼ {X}{now x}   = now∼
refl∼ {X}{later x} = later∼ (♯ refl∼)

sym∼ : ∀{X}{dx dx' : Delay X} → dx ∼ dx' → dx' ∼ dx
sym∼ now∼ = refl∼
sym∼ (later∼ p) = later∼ (♯ (sym∼ (♭ p)))

trans∼ : ∀{X}{dx dx' dx'' : Delay X} → dx ∼ dx' → dx' ∼ dx'' → dx ∼ dx''
trans∼ now∼ now∼ = now∼
trans∼ (later∼ p) (later∼ q) = later∼ (♯ trans∼ (♭ p) (♭ q))

-- convergence

data _↓_ {X : Set} : Delay X → X → Set where
  now↓ : ∀{y} → now y ↓ y
  later↓ : ∀{dy y} → (♭ dy) ↓ y → later dy ↓ y

∼↓ : ∀{X}{dx dy : Delay X}{x : X} → dx ∼ dy → dx ↓ x → dy ↓ x
∼↓ now∼ q = q
∼↓ (later∼ p) (later↓ q) = later↓ (∼↓ (♭ p) q)

unique↓ : ∀{X}{dx : Delay X}{x y : X} → dx ↓ x → dx ↓ y → x ≅ y
unique↓ now↓ now↓ = refl
unique↓ (later↓ p) (later↓ q) = unique↓ p q

-- weak bisimilarity

data _≈_ {X : Set} : Delay X → Delay X → Set where
  ↓≈ : ∀{dy dy' y} → dy ↓ y → dy' ↓ y → dy ≈ dy'
  later≈ : ∀{dy dy'} → ∞ (♭ dy ≈ ♭ dy') → later dy ≈ later dy'

postulate quotient : ∀{X}{dx dx' : Delay X} → dx ≈ dx' → dx ≅ dx'

refl≈ : ∀{X}{dx : Delay X} → dx ≈ dx
refl≈ {dx = now x}    = ↓≈ now↓ now↓
refl≈ {dx = later dx} = later≈ (♯ refl≈)

sym≈ : ∀{X}{dx dx' : Delay X} → dx ≈ dx' → dx' ≈ dx
sym≈ (↓≈ p q) = ↓≈ q p
sym≈ (later≈ p) = later≈ (♯ (sym≈ (♭ p)))

∼→≈ : ∀{X}{dx dy : Delay X} → dx ∼ dy → dx ≈ dy
∼→≈ now∼ = refl≈
∼→≈ (later∼ p) = later≈ (♯ (∼→≈ (♭ p)))

laterlem' : ∀{X}{dx dz : Delay X} → later (♯ dx) ∼ dz → dx ≈ dz
laterlem' {X}{now x}{later dz} (later∼ p) = ↓≈ now↓ (later↓ (∼↓ (♭ p) now↓))
laterlem' {X}{later dx}{later dz} (later∼ p) = 
  later≈ (♯ laterlem' (trans∼ (later∼ (♯ refl∼)) (♭ p)))

laterlem : ∀{X}{dx : Delay X} → dx ≈ later (♯ dx)
laterlem = laterlem' (later∼ (♯ refl∼))

{-
stable≈ : ∀{X}{dx dy dz dw : Delay X} → dx ∼ dy → dy ≈ dz → dz ∼ dw → dx ≈ dw
stable≈ now∼ q now∼ = q
stable≈ now∼ (↓≈ p (later↓ q)) (later∼ r) = ↓≈ p (later↓ (∼↓ (♭ r) q))
stable≈ (later∼ p) (↓≈ (later↓ q) r) now∼ = ↓≈ (later↓ (∼↓ (sym∼ (♭ p)) q)) r
stable≈ (later∼ p) (↓≈ (later↓ q) (later↓ q')) (later∼ r) = 
  later≈ (♯ (stable≈ (♭ p) (↓≈ q q') (♭ r)))
stable≈ (later∼ p) (later≈ q) (later∼ r) = 
  later≈ (♯ (stable≈ (♭ p) (♭ q) (♭ r)))
-}

≈↓ : ∀{X}{dx dy : Delay X}{x : X} → dx ≈ dy → dx ↓ x → dy ↓ x
≈↓ (↓≈ now↓ q) now↓ = q
≈↓ (↓≈ (later↓ p) r) (later↓ q) with unique↓ p q
≈↓ (↓≈ (later↓ p) r) (later↓ q) | refl = r
≈↓ (later≈ p) (later↓ q) = later↓ (≈↓ (♭ p) q)

trans≈ : ∀{X}{dx dy dz : Delay X} → dx ≈ dy → dy ≈ dz → dx ≈ dz
trans≈ (↓≈ p r) (↓≈ q s) with unique↓ r q
trans≈ (↓≈ p r) (↓≈ q s) | refl = ↓≈ p s
trans≈ (↓≈ p (later↓ r)) (later≈ q) = ↓≈ p (later↓ (≈↓ (♭ q) r))
trans≈ (later≈ p) (↓≈ (later↓ q) s) = ↓≈ (later↓ (≈↓ (sym≈ (♭ p)) q)) s
trans≈ (later≈ p) (later≈ q) = later≈ (♯ (trans≈ (♭ p) (♭ q)))

-- monad operations

dbind : ∀{X Y} → (X → Delay Y) → Delay X → Delay Y
dbind f (now x)   = f x
dbind f (later x) = later (♯ dbind f (♭ x))

dbindlater' : ∀{X Y}{f : X → ∞ (Delay Y)}(dx : Delay X)(dz : Delay Y) → 
              later (♯ (dbind (♭ ∘ f) dx)) ∼ dz →
              dbind (later ∘ f) dx ∼ dz
dbindlater' (now x) (now y) ()
dbindlater' (now x) (later y) (later∼ p) = later∼ p
dbindlater' (later x) (now y) ()
dbindlater' (later x) (later y) (later∼ p) = 
  later∼ (♯ dbindlater' (♭ x) (♭ y) (trans∼ (later∼ (♯ refl∼)) (♭ p)))

dbindlater : ∀{X Y}{f : X → ∞ (Delay Y)}(dx : Delay X) → 
             dbind (later ∘ f) dx ∼ later (♯ (dbind (♭ ∘ f) dx))
dbindlater dx = dbindlater' dx _ (later∼ (♯ refl∼))

dbindnowsym' : ∀{X Y Z}{x : X}(dy : Delay Y)(dz : Delay Z)(dx : Delay X) → 
               dbind (λ _ → dbind (λ _ → now x) dz) dy ∼ dx →
               dbind (λ _ → dbind (λ _ → now x) dy) dz ∼ dx 
dbindnowsym' dy (now z) dx p = p
dbindnowsym' dy (later dz) dx p with trans∼ (sym∼ (dbindlater dy)) p
dbindnowsym' dy (later dz) (later dx) p | later∼ q = 
  later∼ (♯ (dbindnowsym' dy (♭ dz) (♭ dx) (♭ q)))

dbindnowsym : ∀{X Y Z}{x : X}(dy : Delay Y)(dz : Delay Z) → 
              dbind (λ _ → dbind (λ _ → now x) dy) dz ∼ 
              dbind (λ _ → dbind (λ _ → now x) dz) dy
dbindnowsym dy dz = dbindnowsym' dy dz _ refl∼

dlaw1 : ∀{X}(dx : Delay X) → dbind now dx ≈ dx
dlaw1 (now x) = refl≈
dlaw1 (later dx) = later≈ (♯ dlaw1 (♭ dx))

--dlaw2 holds definitionally

dlaw3 : ∀{X Y Z}{f : X → Delay Y} {g : Y → Delay Z}(dx : Delay X) → 
        dbind (dbind g ∘ f) dx ≈ dbind g (dbind f dx)
dlaw3 {f = f}{g = g} (now x)   = refl≈
dlaw3 {f = f}{g = g} (later x) = later≈ (♯ dlaw3 (♭ x))


DelayM : Monad Sets
DelayM = record { 
  T    = Delay; 
  η    = now; 
  bind = dbind; 
  law1 = ext (quotient ∘ dlaw1); 
  law2 = refl; 
  law3 = ext (quotient ∘ dlaw3) }

map = Fun.HMap (TFun DelayM)

str : ∀{X Y} → X × Delay Y → Delay (X × Y)
str (x , dy) = map (λ y → (x , y)) dy



{-

-- old version with old _↓_ data type

-- convergence

data _↓_ {X : Set} : Delay X → X → Set where
  now↓ : ∀{y} → now y ↓ y
  later↓' : ∀{dy dz y} → dz ∼ (♭ dy) → dz ↓ y → later dy ↓ y

later↓ : ∀{X dy}{y : X} → (♭ dy) ↓ y → later dy ↓ y
later↓ = later↓' refl∼

∼↓ : ∀{X}{dx dy : Delay X}{x : X} → dx ∼ dy → dx ↓ x → dy ↓ x
∼↓ {X} {now .y} {now y} now∼ q = q
∼↓ {X} {later dx} {later dy} (later∼ p) (later↓' q r) = later↓ (∼↓ (trans∼ q (♭ p)) r)

unique↓ : ∀{X}{dx : Delay X}{x y : X} → dx ↓ x → dx ↓ y → x ≅ y
unique↓ now↓ now↓ = refl
unique↓ (later↓' p p') (later↓' q q') = unique↓ p' (∼↓ (trans∼ q (sym∼ p)) q')

-- weak bisimilarity

data _≈_ {X : Set} : Delay X → Delay X → Set where
  ↓≈ : ∀{dy dy' y} → dy ↓ y → dy' ↓ y → dy ≈ dy'
  later≈ : ∀{dy dy'} → ∞ (♭ dy ≈ ♭ dy') → later dy ≈ later dy'

postulate quotient : ∀{X}{dx dx' : Delay X} → dx ≈ dx' → dx ≅ dx'

refl≈ : ∀{X}{dx : Delay X} → dx ≈ dx
refl≈ {dx = now x}    = ↓≈ now↓ now↓
refl≈ {dx = later dx} = later≈ (♯ refl≈)

sym≈ : ∀{X}{dx dx' : Delay X} → dx ≈ dx' → dx' ≈ dx
sym≈ (↓≈ p q) = ↓≈ q p
sym≈ (later≈ p) = later≈ (♯ (sym≈ (♭ p)))

∼→≈ : ∀{X}{dx dy : Delay X} → dx ∼ dy → dx ≈ dy
∼→≈ now∼ = refl≈
∼→≈ (later∼ p) = later≈ (♯ (∼→≈ (♭ p)))

laterlem' : ∀{X}{dx dz : Delay X} → later (♯ dx) ∼ dz → dx ≈ dz
laterlem' {X}{now x}{later dz} (later∼ p) = ↓≈ now↓ (later↓ (∼↓ (♭ p) now↓))
laterlem' {X}{later dx}{later dz} (later∼ p) = later≈ (♯ laterlem' (trans∼ (later∼ (♯ refl∼)) (♭ p)))

laterlem : ∀{X}{dx : Delay X} → dx ≈ later (♯ dx)
laterlem = laterlem' (later∼ (♯ refl∼))

stable≈ : ∀{X}{dx dy dz dw : Delay X} → dx ∼ dy → dy ≈ dz → dz ∼ dw → dx ≈ dw
stable≈ now∼ q now∼ = q
stable≈ now∼ (↓≈ p (later↓' x q)) (later∼ r) = ↓≈ p (later↓ (∼↓ (♭ r) (∼↓ x q)))
stable≈ (later∼ p) (↓≈ (later↓' x q) r) now∼ = ↓≈ (later↓ (∼↓ (sym∼ (♭ p)) (∼↓ x q))) r
stable≈ (later∼ p) (↓≈ (later↓' x q) (later↓' x₁ q')) (later∼ r) = later≈ (♯ (stable≈ (trans∼ (♭ p) (sym∼ x)) (↓≈ q q') (trans∼ x₁ (♭ r))))
stable≈ (later∼ p) (later≈ x) (later∼ r) = later≈ (♯ (stable≈ (♭ p) (♭ x) (♭ r)))

≈↓ : ∀{X}{dx dy : Delay X}{x : X} → dx ≈ dy → dx ↓ x → dy ↓ x
≈↓ (↓≈ now↓ q) now↓ = q
≈↓ (↓≈ (later↓' p p') r) (later↓' q q') with unique↓ p' (∼↓ (trans∼ q (sym∼ p)) q') 
≈↓ (↓≈ (later↓' p p') r) (later↓' q q') | refl = r
≈↓ (later≈ p) (later↓' q q') = later↓ (≈↓ (stable≈ q (♭ p) refl∼) q')

trans≈ : ∀{X}{dx dx' dx'' : Delay X} → dx ≈ dx' → dx' ≈ dx'' → dx ≈ dx''
trans≈ (↓≈ p r) (↓≈ q s) with unique↓ r q
trans≈ (↓≈ {y = .y} p r) (↓≈ {y = y} q s) | refl = ↓≈ p s
trans≈ (↓≈ now↓ (later↓' q r)) (later≈ s) = ↓≈ now↓ (later↓ (≈↓ (♭ s) (∼↓ q r)))
trans≈ (↓≈ (later↓' p p') (later↓' q r)) (later≈ s) = later≈ (♯ (trans≈ (stable≈ (sym∼ p) (↓≈ p' r) q) (♭ s)))
trans≈ (later≈ p) (↓≈ (later↓' x q) now↓) = ↓≈ (later↓ (≈↓ (sym≈ (♭ p)) (∼↓ x q))) now↓
trans≈ (later≈ p) (↓≈ (later↓' q q') (later↓' r r')) = later≈ (♯ (trans≈ (♭ p) (stable≈ (sym∼ q) (↓≈ q' r') r)))
trans≈ (later≈ p) (later≈ q) = later≈ (♯ (trans≈ (♭ p) (♭ q)))

-- monad operations

dbind : ∀{X Y} → (X → Delay Y) → Delay X → Delay Y
dbind f (now x)   = f x
dbind f (later x) = later (♯ dbind f (♭ x))

dbindlater' : ∀{X Y}(f : X → ∞ (Delay Y))(dx : Delay X)(dz : Delay Y) → 
              later (♯ (dbind (♭ ∘ f) dx)) ∼ dz →
              dbind (later ∘ f) dx ∼ dz
dbindlater' f (now x) (now y) ()
dbindlater' f (now x) (later y) (later∼ p) = later∼ p
dbindlater' f (later x) (now y) ()
dbindlater' f (later x) (later y) (later∼ p) = later∼ (♯ dbindlater' f (♭ x) (♭ y) (trans∼ (later∼ (♯ refl∼)) (♭ p)))

dbindlater : ∀{X Y}(f : X → ∞ (Delay Y))(dx : Delay X) → 
             dbind (later ∘ f) dx ∼ later (♯ (dbind (♭ ∘ f) dx))
dbindlater f dx = dbindlater' f dx _ (later∼ (♯ refl∼))

dlaw1 : ∀{X}(dx : Delay X) → dbind now dx ≈ dx
dlaw1 (now x) = refl≈
dlaw1 (later dx) = later≈ (♯ dlaw1 (♭ dx))

--dlaw2 holds definitionally

dlaw3 : ∀{X Y Z}{f : X → Delay Y} {g : Y → Delay Z}(dx : Delay X) → 
        dbind (dbind g ∘ f) dx ≈ dbind g (dbind f dx)
dlaw3 {f = f}{g = g} (now x)   = refl≈
dlaw3 {f = f}{g = g} (later x) = later≈ (♯ dlaw3 (♭ x))


DelayM : Monad Sets
DelayM = record { 
  T    = Delay; 
  η    = now; 
  bind = dbind; 
  law1 = ext (quotient ∘ dlaw1); 
  law2 = refl; 
  law3 = ext (quotient ∘ dlaw3) }

map = Fun.HMap (TFun DelayM)

str : ∀{X Y} → X × Delay Y → Delay (X × Y)
str (x , dy) = map (λ y → (x , y)) dy
-}