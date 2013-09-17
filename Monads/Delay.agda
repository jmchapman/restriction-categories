
module Monads.Delay where

open import Coinduction
open import Monads
open import Sets
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open import Functors
open import Data.Product renaming (map to pmap)
open import Data.Unit

data Delay (X : Set) : Set where
  now : X → Delay X
  later : ∞ (Delay X) → Delay X

-- Strong bisimilarity

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

-- Convergence

data _↓_ {X : Set} : Delay X → X → Set where
  now↓ : ∀{y} → now y ↓ y
  later↓ : ∀{dy y} → (♭ dy) ↓ y → later dy ↓ y

∼↓ : ∀{X}{dx dy : Delay X}{x : X} → dx ∼ dy → dx ↓ x → dy ↓ x
∼↓ now∼ q = q
∼↓ (later∼ p) (later↓ q) = later↓ (∼↓ (♭ p) q)

unique↓ : ∀{X}{dx : Delay X}{x y : X} → dx ↓ x → dx ↓ y → x ≅ y
unique↓ now↓ now↓ = refl
unique↓ (later↓ p) (later↓ q) = unique↓ p q

-- Weak bisimilarity

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

-- Monad operations

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

{-
-- Strength laws

μ : ∀{X} → Delay (Delay X) → Delay X
μ ddx = dbind (λ dx → dx) ddx

open import Data.Unit

strlaw1 : ∀{X}{dx : Delay X} → map proj₂ (str (tt , dx)) ≈ dx
strlaw1 {X} {now x} = ↓≈ now↓ now↓
strlaw1 {X} {later dx} = later≈ (♯ strlaw1)

strlaw2 : ∀{X Y}{x : X}{y : Y} → str (x , now y) ≈ now (x , y)
strlaw2 = ↓≈ now↓ now↓

α : {X Y Z : Set} → (X × Y) × Z → X × (Y × Z)
α ((x , y) , z) = x , (y , z)

strlaw3 : ∀{X Y Z}{x : X}{y : Y}{dz : Delay Z} → 
          map α (str ((x , y) , dz)) ≈ 
          str (pmap (λ a → a) str (α ((x , y) , dz)))
strlaw3 {X} {Y} {Z} {x} {y} {now z} = ↓≈ now↓ now↓
strlaw3 {X} {Y} {Z} {x} {y} {later dz} = later≈ (♯ strlaw3 {dz = ♭ dz})

strlaw4 : ∀{X Y}{x : X}{ddy : Delay (Delay Y)} → 
          μ (map str (str (x , ddy))) ≈ str (x , (μ ddy))
strlaw4 {ddy = now dy} = refl≈
strlaw4 {ddy = later ddy} = later≈ (♯ (strlaw4 {ddy = ♭ ddy}))
-}


-- Another composition called dcomp, weakly bisimilar to dbind but
-- easier to use.

dbindlater≈ : ∀{X Y}{f : X → ∞ (Delay Y)}(dx : Delay X) → 
              dbind (♭ ∘ f) dx ≈ dbind (later ∘ f) dx
dbindlater≈ dx = trans≈ laterlem 
                        (trans≈ (later≈ (♯ refl≈)) 
                                (∼→≈ (sym∼ (dbindlater dx))))

dcomp : ∀{X Y} → Delay X → Delay Y → Delay Y
dcomp (now x) dy = dy
dcomp (later dx) (now y) = later (♯ (dcomp (♭ dx) (now y)))
dcomp (later dx) (later dy) = later (♯ (dcomp (♭ dx) (♭ dy)))

dcomp↓dbind' : ∀{X Y}{z : Y}(dx : Delay X)(dy dz : Delay Y) → 
               dbind (λ _ → dy) dx ∼ dz → dz ↓ z → dcomp dx dy ↓ z
dcomp↓dbind' (now x) dy dz p q = ∼↓ (sym∼ p) q
dcomp↓dbind' (later dx) (now y) (later .dz) (later∼ p) (later↓ {dz} q) = 
  later↓ (dcomp↓dbind' (♭ dx) (now y) (♭ dz) (♭ p) q)
dcomp↓dbind' (later dx) (later dy) (later .dz) (later∼ p) (later↓ {dz} q) with
  ♭ dz | trans∼ (sym∼ (dbindlater (♭ dx))) (♭ p) 
dcomp↓dbind' (later dx) (later dy) (later .dz) (later∼ p) (later↓ {dz} (later↓ q)) | later dw | later∼ r = later↓ (dcomp↓dbind' (♭ dx) (♭ dy) (♭ dw) (♭ r) q)

dcomp↓dbind : ∀{X Y}{z : Y}(dx : Delay X)(dy : Delay Y) → 
              dbind (λ _ → dy) dx ↓ z → dcomp dx dy ↓ z
dcomp↓dbind dx dy p = dcomp↓dbind' dx dy _ refl∼ p

dcomp≈dbind' : ∀{X Y}(dx : Delay X)(dy dz : Delay Y) → 
               dbind (λ _ → dy) dx ≈ dz → dcomp dx dy ≈ dz
dcomp≈dbind' (now x) dy dz p = p
dcomp≈dbind' (later dx) (now y) (now z) (↓≈ (later↓ p) now↓) 
  = ↓≈ (later↓ (dcomp↓dbind (♭ dx) (now y) p)) now↓
dcomp≈dbind' (later dx) (now y) (later dz) (↓≈ (later↓ p) (later↓ q)) = 
  later≈ (♯ (dcomp≈dbind' (♭ dx) (now y) (♭ dz) (↓≈ p q)))
dcomp≈dbind' (later dx) (now y) (later dz) (later≈ p) = 
  later≈ (♯ (dcomp≈dbind' (♭ dx) (now y) (♭ dz) (♭ p)))
dcomp≈dbind' (later dx) (later dy) (now z) (↓≈ (later↓ p) now↓) = 
  ↓≈ (later↓ (dcomp↓dbind (♭ dx) 
                          (♭ dy) 
                          (≈↓ (sym≈ (dbindlater≈ (♭ dx))) p))) 
      now↓
dcomp≈dbind' (later dx) (later dy) (later dz) (↓≈ (later↓ p) (later↓ q)) = 
  later≈ (♯ (dcomp≈dbind' (♭ dx) 
                          (♭ dy) 
                          (♭ dz) 
                          (trans≈ (dbindlater≈ (♭ dx)) (↓≈ p q))))
dcomp≈dbind' (later dx) (later dy) (later dz) (later≈ p) = 
  later≈ (♯ (dcomp≈dbind' (♭ dx) 
                          (♭ dy) 
                          (♭ dz) 
                          (trans≈ (dbindlater≈ (♭ dx)) (♭ p))))

dcomp≈dbind : ∀{X Y}{dx : Delay X}{dy : Delay Y} → 
              dcomp dx dy ≈ dbind (λ _ → dy) dx
dcomp≈dbind {dx = dx} {dy = dy} = dcomp≈dbind' dx dy _ refl≈ 

-- Some lemmata involving dcomp

dcomp≈fst : ∀{X}{dx dy : Delay X} → dx ≈ dy → dcomp dx dy ≈ dx
dcomp≈fst (↓≈ now↓ now↓) = ↓≈ now↓ now↓
dcomp≈fst {X} {now x} {later dy} (↓≈ now↓ (later↓ p)) = ↓≈ (later↓ p) now↓
dcomp≈fst (↓≈ (later↓ p) now↓) = later≈ (♯ dcomp≈fst (↓≈ p now↓))
dcomp≈fst (↓≈ (later↓ p) (later↓ q)) = later≈ (♯ (dcomp≈fst (↓≈ p q)))
dcomp≈fst (later≈ p) = later≈ (♯ (dcomp≈fst (♭ p)))

dcompcomm : ∀{X Y Z}{dx : Delay X}{dy : Delay Y}{dz : Delay Z} → 
            dcomp dx (dcomp dy dz) ∼ dcomp dy (dcomp dx dz)
dcompcomm {X}{Y}{Z}{now x} {dy} {dz} = refl∼
dcompcomm {X}{Y}{Z}{later dx} {now y} {dz} = refl∼
dcompcomm {X}{Y}{Z}{later dx} {later dy} {now z} = 
  later∼ (♯ dcompcomm {dx = ♭ dx}{dy = ♭ dy})
dcompcomm {X}{Y}{Z}{later dx} {later dy} {later dz} = 
  later∼ (♯ dcompcomm {dx = ♭ dx}{dy = ♭ dy})

dcomp≈→∼ : ∀{X}{dx : Delay X}{x : X} → dcomp dx (now x) ≈ dx → 
           dcomp dx (now x) ∼ dx
dcomp≈→∼ {X}{now x} (↓≈ now↓ now↓) = now∼
dcomp≈→∼ {X}{later dx}(↓≈ (later↓ p) (later↓ q)) = 
  later∼ (♯ (dcomp≈→∼ (↓≈ p q)))
dcomp≈→∼ {X}{later dx}(later≈ p) = later∼ (♯ (dcomp≈→∼ (♭ p)))

dcomp↓snd : ∀{X Y}{dx : Delay X}{dy : Delay Y}{y : Y} → dcomp dx dy ↓ y → dy ↓ y
dcomp↓snd {X}{Y}{now x}{now y} p = p
dcomp↓snd {X}{Y}{later dx}{now y} (later↓ p) = dcomp↓snd {_}{_}{♭ dx} p
dcomp↓snd {X}{Y}{now x}{later dy} p = p
dcomp↓snd {X}{Y}{later dx}{later dy} (later↓ p) = 
  later↓ (dcomp↓snd {_}{_}{♭ dx} p)

-- Meets

_≅'_ : ∀{a b}{A : Set a}{B : Set b} → A → B → Set
a ≅' b = a ≅ b

open import Relation.Binary
open import Relation.Nullary.Core

-- with decidability of equality in codomains

dmeet-aux : ∀{X}{_≟_ : Decidable {A = X} _≅'_} → Delay X → Delay X → Delay X
dmeet-aux {X}{_≟_} (now x) (now y) with x ≟ y
dmeet-aux {X}{_≟_} (now x) (now .x) | yes refl = now x
dmeet-aux {X}{_≟_} (now x) (now y) | no ¬p = 
  later (♯ (dmeet-aux {X}{_≟_} (now x) (now y)))
dmeet-aux {X}{_≟_} (now x) (later dy) = 
  later (♯ (dmeet-aux {X}{_≟_} (now x) (♭ dy)))
dmeet-aux {X}{_≟_} (later dx) (now y) = 
  later (♯ (dmeet-aux {X}{_≟_} (♭ dx) (now y)))
dmeet-aux {X}{_≟_} (later dx) (later dy) = 
  later (♯ (dmeet-aux {X}{_≟_} (♭ dx) (♭ dy)))

dmeet : {X Y : Set}{_≟_ : Decidable {A = Y}{B = Y} _≅'_}
        (f g : X → Delay Y) → X → Delay Y
dmeet {X}{Y}{_≟_} f g x = dmeet-aux {Y}{_≟_} (f x) (g x)

{-
-- with semidecidability of equality in codomains 

data SemiDec {p} (P : Set p) : Set p where
  yes  : ( p :   P) → SemiDec P
  no   : (¬p : ¬ P) → SemiDec P
  wait : SemiDec P → SemiDec P

SemiDecidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
SemiDecidable _∼_ = ∀ x y → SemiDec (x ∼ y)

dmeet-aux : ∀{X}{_≟_ : SemiDecidable {A = X} _≅'_} → Delay X → Delay X → Delay X
dmeet-aux {X}{_≟_} (now x) (now y) with x ≟ y
dmeet-aux {X}{_≟_} (now x) (now .x) | yes refl = now x
dmeet-aux {X}{_≟_} (now x) (now y)  | no ¬p = 
  later (♯ (dmeet-aux {X}{_≟_} (now x) (now y)))
dmeet-aux {X}{_≟_} (now x) (now y)  | wait q = 
  later (♯ (dmeet-aux {X}{_≟_} (now x) (now y)))
dmeet-aux {X}{_≟_} (now x) (later dy) = 
  later (♯ (dmeet-aux {X}{_≟_} (now x) (♭ dy)))
dmeet-aux {X}{_≟_} (later dx) (now y) = 
  later (♯ (dmeet-aux {X}{_≟_} (♭ dx) (now y)))
dmeet-aux {X}{_≟_} (later dx) (later dy) = 
  later (♯ (dmeet-aux {X}{_≟_} (♭ dx) (♭ dy)))

dmeet : {X Y : Set}{_≟_ : SemiDecidable {A = Y}{B = Y} _≅'_}
       (f g : X → Delay Y) → X → Delay Y
dmeet {X}{Y}{_≟_} f g x = dmeet-aux {Y}{_≟_} (f x) (g x)
-}

















{-

-- First product definition. It is the product in Set but not in the
-- Kleisli cat. It is isomorphic to Delay X × Delay Y in Set, and that
-- make me think that there is no way to prove it isomorphic to the
-- actual product (defined in RestrictionDelay.agda) in the Klesli
-- cat.

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

×→D× : ∀{X Y} → Delay X × Delay Y → X D× Y
×→D× (now x , now y) = nownow x y
×→D× (now x , later dy) = nowlater x (♭ dy)
×→D× (later dx , now y) = laternow (♭ dx) y
×→D× (later dx , later dy) = laterlater (♯ (×→D× (♭ dx , ♭ dy)))

u : {X Y Z : Set} → (Z → Delay X) → (Z → Delay Y) → Z → X D× Y
u f g z = ×→D× (f z , g z)

comp-aux₁ : ∀{X Y}(dx : Delay X)(dy : Delay Y) → dproj₁ (×→D× (dx , dy)) ∼ dx
comp-aux₁ (now x) (now y) = now∼
comp-aux₁ (now x) (later dy) = now∼
comp-aux₁ (later dx) (now y) = later∼ (♯ refl∼)
comp-aux₁ (later dx) (later dy) = later∼ (♯ (comp-aux₁ (♭ dx) (♭ dy)))

comp-aux₂ : ∀{X Y}(dx : Delay X)(dy : Delay Y) → dproj₂ (×→D× (dx , dy)) ∼ dy
comp-aux₂ (now x) (now y) = now∼
comp-aux₂ (now x) (later dy) = later∼ (♯ refl∼)
comp-aux₂ (later dx) (now y) = now∼ 
comp-aux₂ (later dx) (later dy) = later∼ (♯ (comp-aux₂ (♭ dx) (♭ dy)))

iso₂ : ∀{X Y}(dxy : X D× Y) → ×→D× (D×→D dxy) D∼ dxy
iso₂ (nownow x y) = nownow∼
iso₂ (nowlater x dy) = nowlater∼ refl∼
iso₂ (laternow dx y) = laternow∼ refl∼
iso₂ (laterlater dxy) = laterlater∼ (♯ (iso₂ (♭ dxy)))

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
-}