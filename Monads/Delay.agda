{-# OPTIONS --type-in-type #-}
module Monads.Delay where

open import Coinduction
open import Categories
open import Monads
open import Categories.Sets
open import Utilities
open import Categories.Functors

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

refl≈ : ∀{X}{dx : Delay X} → dx ≈ dx
refl≈ {dx = now x}    = ↓≈ now↓ now↓
refl≈ {dx = later dx} = later≈ (♯ refl≈)

sym≈ : ∀{X}{dx dx' : Delay X} → dx ≈ dx' → dx' ≈ dx
sym≈ (↓≈ p q) = ↓≈ q p
sym≈ (later≈ p) = later≈ (♯ (sym≈ (♭ p)))

∼→≈ : ∀{X}{dx dy : Delay X} → dx ∼ dy → dx ≈ dy
∼→≈ now∼ = refl≈
∼→≈ (later∼ p) = later≈ (♯ (∼→≈ (♭ p)))

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

≈EqR : ∀{X} → EqR (Delay X)
≈EqR = _≈_ , record {refl = refl≈; sym = sym≈; trans = trans≈ }

QDelay : Set → Set
QDelay X = Quotient.Q (quot (Delay X) ≈EqR)

abs : ∀{X} → Delay X → QDelay X
abs {X} = Quotient.abs (quot (Delay X) ≈EqR)

rep : ∀{X} → QDelay X → Delay X
rep {X} = Quotient.rep (quot (Delay X) ≈EqR)

ax1 : ∀{X}(dx dx' : Delay X) → dx ≈ dx' → abs dx ≅ abs dx'
ax1 {X} = Quotient.ax1 (quot (Delay X) ≈EqR)

ax2 : ∀{X}(dx : QDelay X) → abs (rep dx) ≅ dx
ax2 {X} = Quotient.ax2 (quot (Delay X) ≈EqR)

ax3 : ∀{X}(dx : Delay X) → rep (abs dx) ≈ dx
ax3 {X} = Quotient.ax3 (quot (Delay X) ≈EqR)

laterlem' : ∀{X}{dx dz : Delay X} → later (♯ dx) ∼ dz → dx ≈ dz
laterlem' {X}{now x}{later dz} (later∼ p) = ↓≈ now↓ (later↓ (∼↓ (♭ p) now↓))
laterlem' {X}{later dx}{later dz} (later∼ p) = 
  later≈ (♯ laterlem' (trans∼ (later∼ (♯ refl∼)) (♭ p)))

laterlem : ∀{X}{dx : Delay X} → dx ≈ later (♯ dx)
laterlem = laterlem' (later∼ (♯ refl∼))

laterlem2' : ∀{X}(dx : Delay X){dy}{dz} → dx ≈ later dy → ♭ dy ≈ dz → dx ≈ dz
laterlem2' .dx (↓≈ {dx} p (later↓ p')) q = ↓≈ p (≈↓ q p')
laterlem2' .(later dx) {dy} {now z} (later≈ {dx} p) q = 
  ↓≈ (later↓ (≈↓ (sym≈ (♭ p)) (≈↓ (sym≈ q) now↓))) now↓
laterlem2' .(later dx) {dy} {later dz} (later≈ {dx} p) q = 
  later≈ (♯ (laterlem2' (♭ dx) (trans≈ (♭ p) q) refl≈))

laterlem2 : ∀{X}(dx : Delay X){dy} → dx ≈ later dy → dx ≈ ♭ dy
laterlem2 dx p = laterlem2' dx p refl≈

-- monad operations

dbind : ∀{X Y} → (X → Delay Y) → Delay X → Delay Y
dbind f (now x)   = f x
dbind f (later x) = later (♯ dbind f (♭ x))

dbindcong1↓'' : ∀{X Y}(f : X → Delay Y){x y}{dx : Delay X} → dx ↓ x → 
                f x ≈ now y → dbind f dx ↓ y
dbindcong1↓'' f now↓ q = ≈↓ (sym≈ q) now↓
dbindcong1↓'' f (later↓ p) q = later↓ (dbindcong1↓'' f p q)

dbindcong1↓' : ∀{X Y}(f : X → Delay Y){x}{dx : Delay X} dy → dx ↓ x → 
               f x ≈ dy → dbind f dx ≈ dy
dbindcong1↓' f dy now↓ q = q
dbindcong1↓' f (now y) (later↓ p) q = ↓≈ (later↓ (dbindcong1↓'' f p q)) now↓
dbindcong1↓' f {x} (later dy) (later↓ p) q = 
  later≈ (♯ (dbindcong1↓' f (♭ dy) p (laterlem2 (f x) q)))

dbindcong1↓ : ∀{X Y}(f : X → Delay Y){x}{dx : Delay X} → dx ↓ x → 
              dbind f dx ≈ f x
dbindcong1↓ f p = dbindcong1↓' f _ p refl≈

dbindcong1 : ∀{X Y}(f : X → Delay Y){dx dx' : Delay X} → dx ≈ dx' → 
            dbind f dx ≈ dbind f dx'
dbindcong1 f (↓≈ now↓ now↓) = refl≈
dbindcong1 f {now y} {later dy} (↓≈ now↓ (later↓ q)) = 
  sym≈ (dbindcong1↓ f (later↓ q))
dbindcong1 f {later dy} {now y} (↓≈ (later↓ p) now↓) = dbindcong1↓ f (later↓ p)
dbindcong1 f (↓≈ (later↓ p) (later↓ q)) = later≈ (♯ dbindcong1 f (↓≈ p q))
dbindcong1 f (later≈ p) = later≈ (♯ dbindcong1 f (♭ p))

dbindcong2 : ∀{X Y}{f f' : X → Delay Y} → (∀ x → f x ≈ f' x) → (dx : Delay X) → 
             dbind f dx ≈ dbind f' dx
dbindcong2 p (now x) = p x
dbindcong2 p (later dx) = later≈ (♯ (dbindcong2 p (♭ dx)))

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

open Cat Sets
DelayM : Monad Sets
DelayM = record { 
  T    = QDelay; 
  η    = abs ∘ now;
  bind = λ f dx → abs (dbind (rep ∘ f) (rep dx)); --dbind; 
  law1 = ext λ dx → 
    proof 
    abs (dbind (rep ∘ abs ∘ now) (rep dx)) 
    ≅⟨ ax1 _ _ (dbindcong2 (ax3 ∘ now) (rep dx)) ⟩
    abs (dbind now (rep dx)) 
    ≅⟨ ax1 _ _ (dlaw1 (rep dx)) ⟩ 
    abs (rep dx) 
    ≅⟨ ax2 _ ⟩ 
    dx 
    ∎;
  law2 = λ{X}{Y}{f} → ext λ x → 
    proof
    abs (dbind (rep ∘ f) (rep (abs (now x))))
    ≅⟨ ax1 _ _ (dbindcong1 (rep ∘ f) (ax3 (now x))) ⟩ 
    abs (rep (f x)) 
    ≅⟨ ax2 _ ⟩ 
    f x 
    ∎; 
  law3 = λ{X}{Y}{Z}{f}{g} → ext λ dx → 
    proof
    abs (dbind (rep ∘ abs ∘ dbind (rep ∘ g) ∘ rep ∘ f) (rep dx))
    ≅⟨ ax1 _ _ (dbindcong2 (λ _ → ax3 _) (rep dx)) ⟩
    abs (dbind (dbind (rep ∘ g) ∘ rep ∘ f) (rep dx))
    ≅⟨ ax1 _ _ (dlaw3 (rep dx)) ⟩
    abs (dbind (rep ∘ g) (dbind (rep ∘ f) (rep dx)))
    ≅⟨ ax1 _ _ (dbindcong1 (rep ∘ g) (sym≈ (ax3 _))) ⟩
    abs (dbind (rep ∘ g) (rep (abs (dbind (rep ∘ f) (rep dx)))))
    ∎}


map : ∀{X Y} → (X → Y) → Delay X → Delay Y
map f = dbind (now ∘ f) --rep (Fun.HMap (TFun DelayM) f (abs x))

str : ∀{X Y} → X × Delay Y → Delay (X × Y)
str (x , dy) = map (λ y → (x , y)) dy



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


{-

-- Products

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

u : ∀{X Y Z} → (Z → Delay X) → (Z → Delay Y) → Z → X D× Y
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

Agree : ∀{X Y}(f g : X → Delay Y) → Set
Agree {X} f g = Σ X (λ x → f x ∼ g x)

Meet : ∀{X Y}(f g : X → Delay Y) → Agree f g → Delay Y
Meet f g (x , p) = f x
-}
