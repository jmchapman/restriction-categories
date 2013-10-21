
module Monads.Delay.Iteration where

open import Monads.Delay
open import Coinduction
open import Data.Product hiding (map)
open import Data.Empty renaming (⊥ to ∅)
open import Monads.Delay.Independence
open import Data.Sum

{-

-- Iteration

d† : ∀{X Y} → (X → Delay X) → (X → Delay Y) → Delay X → Delay Y → Delay Y
d† f g (now x) dy = later (♯ (d† f g (f x) (g x)))
d† f g (later dx) (now y) = now y
d† f g (later dx) (later dy) = later (♯ (d† f g (♭ dx) (♭ dy)))

_†_ : ∀{X Y} → (X → Delay X) → (X → Delay Y) → X → Delay Y
(f † g) x = d† f g (f x) (g x)

-- Other (more traditional) definition of iteration

iter' : ∀{X Y} → (X → Delay (X ⊎ Y)) → Delay (X ⊎ Y) → Delay Y
iter' f (now (inj₁ x)) = later (♯ (iter' f (f x)))
iter' f (now (inj₂ y)) = now y
iter' f (later dxy) = later (♯ (iter' f (♭ dxy)))

iter : ∀{X Y} → (X → Delay (X ⊎ Y)) → X → Delay Y
iter f x = iter' f (f x)

-- Two equivalences between the iteration definitions

F' : ∀{X Y} → Delay X → Delay Y → Delay (X ⊎ Y)
F' (now x) dy = now (inj₁ x)
F' (later dx) (now y) = now (inj₂ y)
F' (later dx) (later dy) = later (♯ (F' (♭ dx) (♭ dy)))

F : {X Y Z : Set} → (Z → Delay X) → (Z → Delay Y) → Z → Delay (X ⊎ Y)
F f g z = F' (f z) (g z)

d†→iter' : ∀{X Y}(f : X → Delay X)(g : X → Delay Y) dx dy → 
           d† f g dx dy ≈ iter' (F f g) (F' dx dy)
d†→iter' f g (now x) dy = later≈ (♯ (d†→iter' f g (f x) (g x)))
d†→iter' f g (later dx) (now y) = ↓≈ now↓ now↓
d†→iter' f g (later dx) (later dy) = later≈ (♯ (d†→iter' f g (♭ dx) (♭ dy)))

†→iter : ∀{X Y}(f : X → Delay X)(g : X → Delay Y) x → 
         (f † g) x ≈ iter (F f g) x
†→iter f g x = d†→iter' f g (f x) (g x)

G₁' : ∀{X Y} → Delay (X ⊎ Y) → Delay X
G₁' (now (inj₁ x)) = now x
G₁' (now (inj₂ y)) = later (♯ (G₁' (now (inj₂ y))))
G₁' (later dxy) = later (♯ G₁' (♭ dxy))

G₁'≈never : ∀{X Y : Set}{y : Y} → G₁' (now (inj₂ y)) ≈ never {X}
G₁'≈never = later≈ (♯ G₁'≈never)

G₂' : ∀{X Y} → Delay (X ⊎ Y) → Delay Y
G₂' (now (inj₁ x)) = later (♯ (G₂' (now (inj₁ x))))
G₂' (now (inj₂ y)) = now y
G₂' (later dxy) = later (♯ G₂' (♭ dxy))

G₂'≈never : ∀{X Y : Set}{x : X} → G₂' (now (inj₁ x)) ≈ never {Y}
G₂'≈never = later≈ (♯ G₂'≈never)

G₁ : {X Y Z : Set} → (Z → Delay (X ⊎ Y)) → Z → Delay X
G₁ f z = G₁' (f z)

G₂ : {X Y Z : Set} → (Z → Delay (X ⊎ Y)) → Z → Delay Y
G₂ f z = G₂' (f z)

iter'→d† : ∀{X Y}(f : X → Delay (X ⊎ Y)) dxy → 
           iter' f dxy ≈ d† (G₁ f) (G₂ f) (G₁' dxy) (G₂' dxy)
iter'→d† f (now (inj₁ x)) = later≈ (♯ (iter'→d† f (f x)))
iter'→d† f (now (inj₂ y)) = ↓≈ now↓ now↓
iter'→d† f (later dxy) = later≈ (♯ (iter'→d† f (♭ dxy)))

iter→† : ∀{X Y}(f : X → Delay (X ⊎ Y)) x → 
         iter f x ≈ ((G₁ f) † (G₂ f)) x
iter→† f x = iter'→d† f (f x)

-- For all X and Y we have that 
-- F : Hom(X , Delay X) × Hom(X , Delay Y) → Hom(X , Delay (X + Y) is an 
-- isomorphism and <G₁,G₂> is its inverse iff 
-- Hom (X , Delay X) ⊥ Hom (X , Delay Y), i.e. f ⊥ g for all f : X → Delay X, 
-- g : X → Delay Y

F'G'≈ : ∀{X Y}(dxy : Delay (X ⊎ Y)) → dxy ≈ F' (G₁' dxy) (G₂' dxy)
F'G'≈ (now (inj₁ x)) = ↓≈ now↓ now↓
F'G'≈ (now (inj₂ y)) = ↓≈ now↓ now↓
F'G'≈ (later dxy) = later≈ (♯ (F'G'≈ (♭ dxy)))

FG≈ : ∀{X Y}(f : X → Delay (X ⊎ Y)) x → f x ≈ F (G₁ f) (G₂ f) x
FG≈ f x = F'G'≈ (f x)

G₁'F'≈ : ∀{X Y}{dx : Delay X}{dy : Delay Y} → dx d⊥ dy → dx ≈ G₁' (F' dx dy)
G₁'F'≈ (now⊥later p) = ↓≈ now↓ now↓
G₁'F'≈ (later⊥now p) = 
  later≈ (♯ (trans≈ (d⊥≈never (♭ p)) (sym≈ G₁'≈never)))
G₁'F'≈ (later⊥later p) = later≈ (♯ (G₁'F'≈ (♭ p)))

G₂'F'≈ : ∀{X Y}{dx : Delay X}{dy : Delay Y} → dx d⊥ dy → dy ≈ G₂' (F' dx dy)
G₂'F'≈ (now⊥later p) = 
  later≈ (♯ (trans≈ (d⊥≈never (d⊥sym (♭ p))) (sym≈ G₂'≈never)))
G₂'F'≈ (later⊥now p) = ↓≈ now↓ now↓
G₂'F'≈ (later⊥later p) =   later≈ (♯ (G₂'F'≈ (♭ p)))

G₁F≈ : ∀{X Y}{f : X → Delay X}{g : X → Delay Y} → f ⊥ g → (x : X) →
       f x ≈ G₁ (F f g) x
G₁F≈ p x = G₁'F'≈ (p x)

G₂F≈ : ∀{X Y}{f : X → Delay X}{g : X → Delay Y} → f ⊥ g → (x : X) →
       g x ≈ G₂ (F f g) x
G₂F≈ p x = G₂'F'≈ (p x)
-}

