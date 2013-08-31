
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

-- Products

{-
data _D×_ (X Y : Set) : Set where
  nownow : X → Y → X D× Y
  nowlater : X → Delay Y → X D× Y
  laternow : Delay X → Y → X D× Y
  laterlater : ∞ (X D× Y) → X D× Y

data _D∼_ {X Y : Set} : X D× Y → X D× Y → Set where
  nownow∼ : ∀{x y} → nownow x y D∼ nownow x y
  nowlater∼ : ∀{x dy dy'} → dy ∼ dy' → nowlater x dy D∼ nowlater x dy'
  laternow∼ : ∀{dx dx' y} → dx ∼ dx' → laternow dx y D∼ laternow dx' y
  laterlater∼ : ∀{dxy dxy'} → ∞ (♭ dxy D∼ ♭ dxy') → 
                laterlater dxy D∼ laterlater dxy'

dproj₁ : ∀{X Y} → X D× Y → Delay X
dproj₁ (nownow x y) = now x
dproj₁ (nowlater x dy) = now x
dproj₁ (laternow dx y) = later (♯ dx)
dproj₁ (laterlater dxy) = later (♯ (dproj₁ (♭ dxy)))

dproj₂ : ∀{X Y} → X D× Y → Delay Y
dproj₂ (nownow x y) = now y
dproj₂ (nowlater x dy) = later (♯ dy)
dproj₂ (laternow dx y) = now y
dproj₂ (laterlater dxy) = later (♯ (dproj₂ (♭ dxy)))

D×→D : ∀{X Y} → X D× Y → Delay X × Delay Y
D×→D dxy = (dproj₁ dxy) , (dproj₂ dxy)

×→D× : ∀{X Y} → Delay X → Delay Y → X D× Y
×→D× (now x) (now y) = nownow x y
×→D× (now x) (later dy) = nowlater x (♭ dy)
×→D× (later dx) (now y) = laternow (♭ dx) y
×→D× (later dx) (later dy) = laterlater (♯ (×→D× (♭ dx) (♭ dy)))

u : {X Y Z : Set} → (Z → Delay X) → (Z → Delay Y) → Z → X D× Y
u f g z = ×→D× (f z) (g z)

comp-aux₁ : ∀{X Y}(dx : Delay X)(dy : Delay Y) → dproj₁ (×→D× dx dy) ∼ dx
comp-aux₁ (now x) (now y) = now∼
comp-aux₁ (now x) (later dy) = now∼
comp-aux₁ (later dx) (now y) = later∼ (♯ refl∼)
comp-aux₁ (later dx) (later dy) = later∼ (♯ (comp-aux₁ (♭ dx) (♭ dy)))

comp-aux₂ : ∀{X Y}(dx : Delay X)(dy : Delay Y) → dproj₂ (×→D× dx dy) ∼ dy
comp-aux₂ (now x) (now y) = now∼
comp-aux₂ (now x) (later dy) = later∼ (♯ refl∼)
comp-aux₂ (later dx) (now y) = now∼ 
comp-aux₂ (later dx) (later dy) = later∼ (♯ (comp-aux₂ (♭ dx) (♭ dy)))

comp₁ : ∀{X Y Z}(f : Z → Delay X)(g : Z → Delay Y)(z : Z) → 
        dproj₁ (u f g z) ∼ f z
comp₁ f g z = comp-aux₁ (f z) (g z)

comp₂ : ∀{X Y Z}(f : Z → Delay X)(g : Z → Delay Y)(z : Z) → 
        dproj₂ (u f g z) ∼ g z
comp₂ f g z = comp-aux₂ (f z) (g z)

uniq-aux : ∀{X Y}(dxy dxy' : X D× Y) → dproj₁ dxy ∼ dproj₁ dxy' → 
           dproj₂ dxy ∼ dproj₂ dxy' → dxy D∼ dxy'
uniq-aux (nownow x y) (nownow .x .y) now∼ now∼ = nownow∼
uniq-aux (nownow x x₁) (nowlater x₂ x₃) p ()
uniq-aux (nownow x x₁) (laternow x₂ x₃) () q
uniq-aux (nownow x x₁) (laterlater x₂) () q
uniq-aux (nowlater x x₁) (nownow x₂ x₃) p ()
uniq-aux (nowlater x dy) (nowlater .x dy') now∼ (later∼ q) = nowlater∼ (♭ q)
uniq-aux (nowlater x x₁) (laternow x₂ x₃) p ()
uniq-aux (nowlater x x₁) (laterlater x₂) () q
uniq-aux (laternow x x₁) (nownow x₂ x₃) () q
uniq-aux (laternow x x₁) (nowlater x₂ x₃) p ()
uniq-aux (laternow dx y) (laternow dx' .y) (later∼ p) now∼ = laternow∼ (♭ p)
uniq-aux (laternow x x₁) (laterlater x₂) p ()
uniq-aux (laterlater x) (nownow x₁ x₂) () q
uniq-aux (laterlater x) (nowlater x₁ x₂) () q
uniq-aux (laterlater x) (laternow x₁ x₂) p ()
uniq-aux (laterlater dxy) (laterlater dxy') (later∼ p) (later∼ q) = 
  laterlater∼ (♯ (uniq-aux (♭ dxy) (♭ dxy') (♭ p) (♭ q)))

uniq : ∀{X Y Z}(f : Z → Delay X)(g : Z → Delay Y)(u' : Z → X D× Y)(z : Z) → 
       dproj₁ (u' z) ∼ f z → dproj₂ (u' z) ∼ g z → u' z D∼ u f g z
uniq f g u' z p q = uniq-aux (u' z) 
                             (u f g z) 
                             (trans∼ p (sym∼ (comp₁ f g z))) 
                             (trans∼ q (sym∼ (comp₂ f g z)))

-- Meets

meet-aux : ∀{X}(y : X)(dx : Delay X) → Delay ((x : X) → y ≅ {!y!})
meet-aux y (now x) = {!!}
meet-aux y (later dx) = {!!}

meet : ∀{X Y}(f g : X → Delay Y) → X → Delay {!!}
meet f g x = {!!}
-}