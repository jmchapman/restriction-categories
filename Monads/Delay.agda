{-# OPTIONS --type-in-type #-}
module Monads.Delay where

open import Coinduction
open import Categories
open import Monads
open import Categories.Sets
open import Utilities
open import Categories.Functors

mutual
  data Delay (X : Set) : Set where
    now : X → Delay X
    later : ∞Delay X → Delay X

  record ∞Delay (X : Set) : Set where
    coinductive
    field force : Delay X
open ∞Delay

-- strong bisimilarity
mutual 
  data _~_ {X : Set} : Delay X → Delay X → Set where
    now~ : ∀{x} → now x ~ now x
    later~ : ∀{dy dy'} → dy ∞~ dy' → later dy ~ later dy'

  record _∞~_ {X : Set}(dx : ∞Delay X)(dx' : ∞Delay X) : Set where
    coinductive
    field ~force : force dx ~ force dx'
open _∞~_

mutual 
  refl~ : ∀{X}(dx : Delay X) → dx ~ dx
  refl~ (now x)    = now~
  refl~ (later dx) = later~ (refl∞~ dx)

  refl∞~ : ∀{X}(dx : ∞Delay X) → dx ∞~ dx
  ~force (refl∞~ dx) = refl~ (force dx)

mutual
  sym~ : ∀{X}{dx dx' : Delay X} → dx ~ dx' → dx' ~ dx
  sym~ now~       = now~
  sym~ (later~ p) = later~ (sym∞~ p)

  sym∞~ : ∀{X}{dx dx' : ∞Delay X} → dx ∞~ dx' → dx' ∞~ dx
  ~force (sym∞~ p) = sym~ (~force p)

mutual
  trans~ : ∀{X}{dx dx' dx'' : Delay X} → 
           dx ~ dx' → dx' ~ dx'' → dx ~ dx''
  trans~ now~       now~       = now~
  trans~ (later~ p) (later~ q) = later~ (trans∞~ p q)

  trans∞~ : ∀{X}{dx dx' dx'' : ∞Delay X} → 
            dx ∞~ dx' → dx' ∞~ dx'' → dx ∞~ dx''
  ~force (trans∞~ p q) = trans~ (~force p) (~force q)

-- convergence
data _↓_ {X : Set} : Delay X → X → Set where
  now↓ : ∀{y} → now y ↓ y
  later↓ : ∀{dy y} → (force dy) ↓ y → later dy ↓ y


det~↓ : ∀{X}{dx dy : Delay X}{x : X} → dx ~ dy → dx ↓ x → dy ↓ x
det~↓ now~       q = q
det~↓ (later~ p) (later↓ q) = later↓ (det~↓ (~force p) q)

-- Delay is a monad up to strong bisimilarity
mutual
  dbind : ∀{X Y} → (X → Delay Y) → Delay X → Delay Y
  dbind f (now x)   = f x
  dbind f (later x) = later (∞dbind f x)

  ∞dbind : ∀{X Y} → (X → Delay Y) → ∞Delay X → ∞Delay Y
  force (∞dbind f x) = dbind f (force x)

mutual
  dlaw1 : ∀{X}(dx : Delay X) →  dbind now dx ~ dx
  dlaw1 (now x)   = now~
  dlaw1 (later x) = later~ (∞dlaw1 x)

  ∞dlaw1 : ∀{X}(dx : ∞Delay X) →  ∞dbind now dx ∞~ dx
  ~force (∞dlaw1 dx) = dlaw1 (force dx)

mutual
  dlaw3 : ∀{X Y Z}
          {f : X → Delay Y}
          {g : Y → Delay Z}(dx : Delay X) →
          dbind (dbind g ∘ f) dx ~ dbind g (dbind f dx)
  dlaw3 (now x)   = refl~ _
  dlaw3 (later x) = later~ (∞dlaw3 x)

  ∞dlaw3 : ∀{X Y Z}
          {f : X → Delay Y}
          {g : Y → Delay Z}(dx : ∞Delay X) →
          ∞dbind (dbind g ∘ f) dx ∞~ ∞dbind g (∞dbind f dx)
  ~force (∞dlaw3 dx) = dlaw3 (force dx)

{-
Delay~M : Monad Sets
Delay~M = record
  { T    = Delay 
  ; η    = now 
  ; bind = dbind 
  ; law1 = {!!} 
  ; law2 = refl 
  ; law3 = {!!} }
-}

{-
unique↓ : ∀{X}{dx : Delay X}{x y : X} → dx ↓ x → dx ↓ y → x ≅ y
unique↓ now↓ now↓ = refl
unique↓ (later↓ p) (later↓ q) = unique↓ p q

data _↯_ {X : Set} : Delay X → Delay X → Set where
  ∼↯ : ∀{c c'} → c ∼ c' → c ↯ c'
  later↯ : ∀{c c'} → ♭ c ↯ c' → later c ↯ c'

↯→↓ : ∀{X}{x : X}{c} → c ↯ now x → c ↓ x
↯→↓ (∼↯ now∼) = now↓
↯→↓ (later↯ p) = later↓ (↯→↓ p)

↓→↯ : ∀{X}{x : X}{c} → c ↓ x → c ↯ now x
↓→↯ now↓ = ∼↯ now∼
↓→↯ (later↓ p) = later↯ (↓→↯ p)

trans↯ : ∀{X}{c d e : Delay X} → c ↯ d → d ↯ e → c ↯ e
trans↯ (∼↯ p) (∼↯ q) = ∼↯ (trans∼ p q)
trans↯ (∼↯ (later∼ p)) (later↯ q) = later↯ (trans↯ (∼↯ (♭ p)) q)
trans↯ (later↯ p) q = later↯ (trans↯ p q)
-}

-- weak bisimilarity

mutual 
  data _≈_ {X : Set} : Delay X → Delay X → Set where
    ↓≈ : ∀{dy dy' y} → dy ↓ y → dy' ↓ y → dy ≈ dy'
    later≈ : ∀{dy dy'} → dy ∞≈ dy' → later dy ≈ later dy'
  
  record _∞≈_ {X : Set}(dx dx' : ∞Delay X) : Set where
    coinductive
    field ≈force : force dx ≈ force dx'
open _∞≈_

mutual 
  refl≈ : ∀{X}(dx : Delay X) → dx ≈ dx
  refl≈ (now x)   = ↓≈ now↓ now↓
  refl≈ (later x) = later≈ (refl∞≈ x)

  refl∞≈ : ∀{X}(dx : ∞Delay X) → dx ∞≈ dx
  ≈force (refl∞≈ dx) = refl≈ (force dx)

mutual
  sym≈ : ∀{X}{dx dx' : Delay X} → dx ≈ dx' → dx' ≈ dx
  sym≈ (↓≈ p q)   = ↓≈ q p
  sym≈ (later≈ p) = later≈ (sym∞≈ p)

  sym∞≈ : ∀{X}{dx dx' : ∞Delay X} → dx ∞≈ dx' → dx' ∞≈ dx
  ≈force (sym∞≈ p) = sym≈ (≈force p)

det≈↓ : ∀{X}{dx dy : Delay X}{x : X} → dx ≈ dy → dx ↓ x → dy ↓ x
det≈↓ (↓≈ now↓ q)       now↓       = q
det≈↓ (↓≈ (later↓ p) q) (later↓ r) = det≈↓ (↓≈ p q) r
det≈↓ (later≈ p)        (later↓ q) = later↓ (det≈↓ (≈force p) q)

mutual
  trans≈ : ∀{X}{dx dy dz : Delay X} → dx ≈ dy → dy ≈ dz → dx ≈ dz
  trans≈ (later≈ p) (later≈ q) = later≈ (trans∞≈ p q)
  trans≈ (↓≈ p q)   r          = ↓≈ p (det≈↓ r q)
  trans≈ p          (↓≈ q r)   = ↓≈ (det≈↓ (sym≈ p) q) r

  trans∞≈ : ∀{X}{dx dy dz : ∞Delay X} → dx ∞≈ dy → dy ∞≈ dz → dx ∞≈ dz
  ≈force (trans∞≈ p q) = trans≈ (≈force p) (≈force q)

mutual
  ~→≈ : ∀{X}{dx dy : Delay X} → dx ~ dy → dx ≈ dy
  ~→≈ now~ = refl≈ _
  ~→≈ (later~ p) = later≈ (∞~→≈ p)

  ∞~→≈ : ∀{X}{dx dy : ∞Delay X} → dx ∞~ dy → dx ∞≈ dy
  ≈force (∞~→≈ p) = ~→≈ (~force p)

≈EqR : ∀{X} → EqR (Delay X)
≈EqR = _≈_ , record {refl = refl≈ _; sym = sym≈; trans = trans≈ }

dlaw1≈ : ∀{X}(dx : Delay X) → dbind now dx ≈ dx
dlaw1≈ = ~→≈ ∘ dlaw1

dlaw3≈ : ∀{X Y Z}
         {f : X → Delay Y}
         {g : Y → Delay Z}(dx : Delay X) →
         dbind (dbind g ∘ f) dx ≈ dbind g (dbind f dx)
dlaw3≈ = ~→≈ ∘ dlaw3

{-
Delay≈M : Monad Sets
Delay≈M = record
  { T    = Delay 
  ; η    = now 
  ; bind = dbind 
  ; law1 = {!!} 
  ; law2 = refl 
  ; law3 = {!!} }
-}


-- Quotienting Delay by weak bisimilarity

QDelay : Set → Set
QDelay X = Quotient.Q (quot (Delay X) ≈EqR)

abs : ∀{X} → Delay X → QDelay X
abs {X} = Quotient.abs (quot (Delay X) ≈EqR)

compat : ∀{X}(Y : QDelay X → Set) → ((x : Delay X) → Y (abs x)) → Set
compat {X} = Quotient.compat (quot (Delay X) ≈EqR)

lift : ∀{X}(Y : QDelay X → Set)(f : (x : Delay X) → Y (abs x)) → 
       (compat {X} Y f) → (q : QDelay X) → Y q
lift {X} = Quotient.lift (quot (Delay X) ≈EqR)

sound : ∀{X}{dx dx' : Delay X} → dx ≈ dx' → abs dx ≅ abs dx'
sound {X} = Quotient.sound (quot (Delay X) ≈EqR)

liftbeta : ∀{X}(Y : QDelay X → Set)(f : (x : Delay X) → Y (abs x))
       (p : compat {X} Y f)(x : Delay X) →  (lift {X} Y f p) (abs x) ≅ f x
liftbeta {X} = Quotient.liftbeta (quot (Delay X) ≈EqR)

{-
QDelay-map : (X Y : Set) → Set
QDelay-map X Y = Quotient.Q (quot (X → Delay Y) (EqR→ ≈EqR))

abs-map : ∀{X Y} → (X → Delay Y) → QDelay-map X Y
abs-map {X}{Y} = Quotient.abs (quot (X → Delay Y) (EqR→ ≈EqR))

compat-map : ∀{X Y}{Z : QDelay-map X Y → Set} → 
             ((f : X → Delay Y) → Z (abs-map f)) → Set
compat-map {X}{Y}{Z} = Quotient.compat (quot (X → Delay Y) (EqR→ ≈EqR)) {Z}

lift-map : ∀{X Y}{Z : QDelay-map X Y → Set}
           (F : (f : X → Delay Y) → Z (abs-map f)) → 
           .(compat-map {X}{Y}{Z} F) → (q : QDelay-map X Y) → Z q
lift-map {X}{Y} = Quotient.lift (quot (X → Delay Y) (EqR→ ≈EqR))

.ax1-map : ∀{X Y}(f g : X → Delay Y) → map~ ≈EqR f g → abs-map f ≅ abs-map g
ax1-map {X}{Y} = Quotient.ax1 (quot (X → Delay Y) (EqR→ ≈EqR))

.ax3-map : ∀{X Y}{Z : QDelay-map X Y → Set}
           (F : (f : X → Delay Y) → Z (abs-map f))(p : compat-map {X}{Y}{Z} F)
           (f : X → Delay Y) → (lift-map {X}{Y}{Z} F p) (abs-map f) ≅ F f
ax3-map {X}{Y} = Quotient.ax3 (quot (X → Delay Y) (EqR→ ≈EqR))

--~→map~ : ∀{X Y} → (X → QDelay Y) → QDelay-map X Y
--~→map~ = proj₁ quotiso

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

-- Equivalent formulations of weak bisimilarity

data _≈'_ {X : Set} : Delay X → Delay X → Set where
 now≈'    : ∀{x} → now x ≈' now x
 laterl≈' : ∀{x c} → ♭ c ↓ x → later c ≈' now x
 laterr≈' : ∀{x c} → ♭ c ↓ x → now x ≈' later c
 later≈'  : ∀{c c'} → ∞ (♭ c ≈' ♭ c') → later c ≈' later c'

≈'→≈ : ∀{X}{x y : Delay X} → x ≈' y → x ≈ y
≈'→≈ now≈' = ↓≈ now↓ now↓
≈'→≈ (laterl≈' p) = ↓≈ (later↓ p) now↓
≈'→≈ (laterr≈' p) = ↓≈ now↓ (later↓ p)
≈'→≈ (later≈' p) = later≈ (♯ (≈'→≈ (♭ p)))

≈→≈' : ∀{X}{x y : Delay X} → x ≈ y → x ≈' y
≈→≈' (↓≈ now↓ now↓) = now≈'
≈→≈' (↓≈ now↓ (later↓ q)) = laterr≈' q
≈→≈' (↓≈ (later↓ p) now↓) = laterl≈' p
≈→≈' (↓≈ (later↓ p) (later↓ q)) = later≈' (♯ (≈→≈' (↓≈ p q)))
≈→≈' (later≈ p) = later≈' (♯ (≈→≈' (♭ p)))

data _≈''_ {X : Set} : Delay X → Delay X → Set where
  nowl≈'' : ∀{c x} → c ↓ x → now x ≈'' c
  nowr≈'' : ∀{c x} → c ↓ x → c ≈'' now x
  ↯≈''    : ∀{c c' d d'} → ♭ c ↯ d → ♭ c' ↯ d' → ∞ (d ≈'' d') → 
            later c ≈'' later c'

≈''-lemma : ∀{X}{c c' d d' : Delay X} → c ↯ d → c' ↯ d' → d ≈'' d' → c ≈'' c'
≈''-lemma (∼↯ now∼) (∼↯ now∼) r = r
≈''-lemma (∼↯ now∼) (∼↯ (later∼ q)) (nowl≈'' (later↓ r)) = nowl≈'' (later↓ (∼↓ (sym∼ (♭ q)) r))
≈''-lemma (∼↯ (later∼ p)) (∼↯ now∼) (nowr≈'' (later↓ r)) = nowr≈'' (later↓ (∼↓ (sym∼ (♭ p)) r))
≈''-lemma (∼↯ (later∼ p)) (∼↯ (later∼ q)) (↯≈'' r s t) = ↯≈'' (∼↯ (♭ p)) (∼↯ (♭ q)) (♯ (≈''-lemma r s (♭ t)))
≈''-lemma (∼↯ now∼) (later↯ q) (nowl≈'' now↓) = nowl≈'' (later↓ (↯→↓ q))
≈''-lemma (∼↯ now∼) (later↯ q) (nowl≈'' (later↓ r)) = nowl≈'' (later↓ (↯→↓ (trans↯ q (later↯ (↓→↯ r)))))
≈''-lemma (∼↯ now∼) (later↯ q) (nowr≈'' now↓) = nowl≈'' (later↓ (↯→↓ q))
≈''-lemma (∼↯ (later∼ p)) (later↯ q) (nowr≈'' (later↓ r)) = ↯≈'' (∼↯ (♭ p)) q (♯ (nowr≈'' r))
≈''-lemma (∼↯ (later∼ p)) (later↯ q) (↯≈'' r s t) = ↯≈'' (∼↯ (♭ p)) (trans↯ q (later↯ (∼↯ refl∼))) (♯ ≈''-lemma r s (♭ t))
≈''-lemma (later↯ p) (∼↯ now∼) (nowl≈'' now↓) = nowr≈'' (later↓ (↯→↓ p))
≈''-lemma (later↯ p) (∼↯ now∼) (nowr≈'' r) = nowr≈'' (later↓ (↯→↓ (trans↯ p (↓→↯ r))))
≈''-lemma (later↯ p) (∼↯ (later∼ q)) (nowl≈'' (later↓ r)) = ↯≈'' p (∼↯ (♭ q)) (♯ (nowl≈'' r))
≈''-lemma (later↯ p) (∼↯ (later∼ q)) (↯≈'' r s t) = ↯≈'' (trans↯ p (later↯ (∼↯ refl∼))) (∼↯ (♭ q)) (♯ (≈''-lemma r s (♭ t)))
≈''-lemma (later↯ p) (later↯ q) r = ↯≈'' p q (♯ r)

≈''→≈ : ∀{X}{x y : Delay X} → x ≈'' y → x ≈ y
≈''→≈ (nowl≈'' p) = ↓≈ now↓ p
≈''→≈ (nowr≈'' p) = ↓≈ p now↓
≈''→≈ (↯≈'' p q r) = later≈ (♯ ≈''→≈ (≈''-lemma p q (♭ r)))

≈→≈'' : ∀{X}{x y : Delay X} → x ≈ y → x ≈'' y
≈→≈'' (↓≈ now↓ now↓) = nowl≈'' now↓
≈→≈'' (↓≈ now↓ (later↓ q)) = nowl≈'' (later↓ q)
≈→≈'' (↓≈ (later↓ p) now↓) = nowr≈'' (later↓ p)
≈→≈'' (↓≈ (later↓ p) (later↓ q)) = 
  ↯≈'' (∼↯ refl∼) (∼↯ refl∼) (♯ (≈→≈'' (↓≈ p q)))
≈→≈'' (later≈ p) = ↯≈'' (∼↯ refl∼) (∼↯ refl∼) (♯ (≈→≈'' (♭ p)))

-- monad operations

dbindcong1∼ : ∀{X Y}(f : X → Delay Y){dx dx' : Delay X} → dx ∼ dx' → 
              dbind f dx ∼ dbind f dx'
dbindcong1∼ f now∼ = refl∼
dbindcong1∼ f (later∼ p) = later∼ (♯ (dbindcong1∼ f (♭ p)))

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

dlaw1∼ : ∀{X}(dx : Delay X) → dbind now dx ∼ dx
dlaw1∼ (now x) = refl∼
dlaw1∼ (later dx) = later∼ (♯ dlaw1∼ (♭ dx))

--dlaw2 holds definitionally

dlaw3∼ : ∀{X Y Z}{f : X → Delay Y} {g : Y → Delay Z}(dx : Delay X) → 
         dbind (dbind g ∘ f) dx ∼ dbind g (dbind f dx)
dlaw3∼ {f = f}{g = g} (now x)   = refl∼
dlaw3∼ {f = f}{g = g} (later x) = later∼ (♯ dlaw3∼ (♭ x))

dlaw1 : ∀{X}(dx : Delay X) → dbind now dx ≈ dx
dlaw1 dx = ∼→≈ (dlaw1∼ dx)

dlaw3 : ∀{X Y Z}{f : X → Delay Y} {g : Y → Delay Z}(dx : Delay X) → 
        dbind (dbind g ∘ f) dx ≈ dbind g (dbind f dx)
dlaw3 dx = ∼→≈ (dlaw3∼ dx)

open Cat Sets
open Lift₂

.compat-abs-dbind : ∀{X Y} → compat₂ (quot (X → Delay Y) (EqR→ ≈EqR))
                                     (quot (Delay X) ≈EqR)
                                     (λ g x → abs (dbind g x))
compat-abs-dbind {X}{Y}{f}{_}{_}{y} p q = ax1 _ _ (trans≈ (dbindcong1 f q) 
                                                          (dbindcong2 p y))

qbind : ∀{X Y} → (X → QDelay Y) → QDelay X → QDelay Y
qbind {X}{Y} f = 
  lift₂ (quot (X → Delay Y) (EqR→ ≈EqR)) 
        (quot (Delay X) ≈EqR)
        (λ g x → abs (dbind g x)) 
        compat-abs-dbind 
        (~→map~ f)

.qbindabs : ∀{X Y}{f : X → QDelay Y}{x : Delay X} →
            qbind f (abs x) ≅ 
            lift-map (λ g → abs (dbind g x)) 
                     (λ r → compat-abs-dbind r (irefl (proj₂ ≈EqR))) 
                     (~→map~ f)
qbindabs {X}{Y}{f}{x} = lift₂→lift' (quot (X → Delay Y) (EqR→ ≈EqR))
                                     (quot (Delay X) ≈EqR)
                                     (λ g y → abs (dbind g y))
                                     compat-abs-dbind
                                     (~→map~ f)
                                     x

.qbindabsabs : ∀{X Y}{f : X → Delay Y}{x : Delay X} →
               qbind (abs ∘ f) (abs x) ≅ abs (dbind f x)
qbindabsabs {X}{Y}{f}{x} = 
  proof
  qbind (abs ∘ f) (abs x) 
  ≅⟨ qbindabs ⟩ 
  lift-map {Z = λ _ → QDelay Y}
           (λ g → abs (dbind g x)) 
           (λ r → compat-abs-dbind r (irefl (proj₂ ≈EqR))) 
           (~→map~ (abs ∘ f))
  ≅⟨ cong
       (λ g →
          lift-map {Z = λ _ → QDelay Y} (λ g₁ → abs (dbind g₁ x))
          (λ r → compat-abs-dbind r (irefl (proj₂ ≈EqR))) (g f))
       (~→map~-abs {X}{Delay Y}{≈EqR}) ⟩
  lift-map {Z = λ _ → QDelay Y}
           (λ g → abs (dbind g x)) 
           (λ r → compat-abs-dbind r (irefl (proj₂ ≈EqR))) 
           (abs-map f)
  ≅⟨ ax3-map {Z = λ _ → QDelay Y}
             (λ g → abs (dbind g x)) 
             (λ r → compat-abs-dbind r (irefl (proj₂ ≈EqR))) 
             f ⟩
  abs (dbind f x)
  ∎

.~→map~-abs-delay : ∀{X}{Y}(f : X → Delay Y) → ~→map~ (abs ∘ f) ≅ abs-map f
~→map~-abs-delay f = cong (λ g → g f) ~→map~-abs 

.qlaw1 : ∀{X} → qbind {X}{X} (abs ∘ now) ≅ iden {QDelay X}
qlaw1 {X} = ext (λ q → 
  lift {Y = λ y → qbind (abs ∘ now) y ≅ y}
       (λ x →                  
         proof
         qbind (abs ∘ now) (abs x)
         ≅⟨ qbindabsabs ⟩
         abs (dbind now x)                
         ≅⟨ ax1 _ _ (dlaw1 x) ⟩
         abs x
         ∎)
       (λ x → fixtypes' (cong (qbind (abs ∘ now)) (ax1 _ _ x))) 
       q)

.qlaw2 : ∀{X Y}{f : X → QDelay Y} → (qbind f) ∘ (abs ∘ now) ≅ f
qlaw2 {X}{Y}{f} = ext (λ x → 
  proof
  qbind f (abs (now x))
  ≅⟨ qbindabs ⟩
  lift-map (λ g → abs (g x)) (λ p → ax1 _ _ (p x)) (~→map~ f)
  ≅⟨ lift-map-abs ⟩
  lift-map {Z = λ _ → X → QDelay Y} 
           (λ g → abs ∘ g) 
           (λ p → ext (λ a → ax1 _ _ (p a))) 
           (~→map~ f) 
           x
  ≡⟨⟩
  map~→~ (~→map~ f) x
  ≅⟨ cong (λ g → g x) ~iso2 ⟩
  f x
  ∎)

.qlaw3 : ∀{X Y Z}{f : X → QDelay Y}{g : Y → QDelay Z} →
         qbind ((qbind g) ∘ f) ≅ (qbind g) ∘ (qbind f)
qlaw3 {X}{Y}{Z}{f}{g} = ext (λ q → 
  lift {Y = λ y → qbind (comp (qbind g) f) y ≅ comp (qbind g) (qbind f) y } 
       (λ x → 
         proof
         qbind ((qbind g) ∘ f) (abs x) 
         ≅⟨ qbindabs ⟩ 
         lift-map {Z = λ _ → QDelay Z} 
                  (λ h → abs (dbind h x)) 
                  (λ p → ax1 _ _ (dbindcong2 p x)) 
                  (~→map~ ((qbind g) ∘ f))
         ≅⟨ lift-map
              {Z =
               λ y →
                 lift-map {Z = λ _ → QDelay Z} (λ h → abs (dbind h x))
                 (λ p → ax1 _ _ (dbindcong2 p x))
                 (~→map~
                  (lift₂ (quot (Y → Delay Z) (EqR→ ≈EqR)) (quot (Delay Y) ≈EqR)
                   (λ h x₁ → abs (dbind h x₁)) compat-abs-dbind y
                   ∘ f))
                 ≅
                 lift₂ (quot (Y → Delay Z) (EqR→ ≈EqR))
                 (quot (X → Delay Y) (EqR→ ≈EqR))
                 (λ h l → abs (dbind (dbind h ∘ l) x))
                 (λ {h} {_} {_} {l} p r →
                    ax1 _ _
                    (dbindcong2
                     (λ y₁ → trans≈ (dbindcong1 h (r y₁)) (dbindcong2 p (l y₁))) x))
                 y (~→map~ f)}
              (λ h → 
                proof
                lift-map {Z = λ _ → QDelay Z} 
                         (λ h → abs (dbind h x))
                         (λ p → ax1 _ _ (dbindcong2 p x))
                         (~→map~ (λ y → lift₂ (quot (Y → Delay Z) (EqR→ ≈EqR)) 
                                              (quot (Delay Y) ≈EqR)
                                              (λ h x₁ → abs (dbind h x₁)) 
                                              compat-abs-dbind
                                              (abs-map h)
                                              (f y)))
                ≅⟨ cong (λ z → lift-map {Z = λ _ → QDelay Z} 
                                        (λ h → abs (dbind h x))
                                        (λ p → ax1 _ _ (dbindcong2 p x))
                                        (~→map~ z))
                        (ext (λ y → lift₂→lift (quot (Y → Delay Z) (EqR→ ≈EqR)) 
                                               (quot (Delay Y) ≈EqR)
                                               (λ h x₁ → abs (dbind h x₁)) 
                                               compat-abs-dbind
                                               h
                                               (f y))) ⟩
                lift-map {Z = λ _ → QDelay Z}
                         (λ l → abs (dbind l x))
                         (λ p → ax1 _ _ (dbindcong2 p x))
                         (~→map~ (λ y → lift (abs ∘ dbind h) 
                                             (compat-abs-dbind (irefl (proj₂ (EqR→ ≈EqR))))
                                             (f y)))
                ≅⟨ cong
                     (lift-map {Z = λ _ → QDelay Z} (λ l → abs (dbind l x))
                      (λ p → ax1 _ _ (dbindcong2 p x)))
                     (~⇢map~-naturality f) ⟩
                lift-map {Z = λ _ → QDelay Z}
                         (λ l → abs (dbind l x))
                         (λ p → ax1 _ _ (dbindcong2 p x))
                         (lift-map {Z = λ _ → QDelay-map X Z}
                                   (λ l → abs-map (dbind h ∘ l)) 
                                   (λ r → ax1-map _ _ (λ y → dbindcong1 h (r y))) 
                                   (~→map~ f))
                ≅⟨ lift-map
                     {Z =
                      λ y →
                        lift-map {Z = λ _ → QDelay Z} (λ l → abs (dbind l x))
                        (λ p → ax1 _ _ (dbindcong2 p x))
                        (lift-map {Z = λ _ → QDelay-map X Z} (λ l → abs-map (dbind h ∘ l))
                         (λ r → ax1-map _ _ (λ y₁ → dbindcong1 h (r y₁))) y)
                        ≅
                        lift-map {Z = λ _ → QDelay Z} (λ l → abs (dbind (dbind h ∘ l) x))
                        (λ r → ax1 _ _ (dbindcong2 (λ x₁ → dbindcong1 h (r x₁)) x)) y}
                     (λ l → 
                       proof
                       lift-map {Z = λ _ → QDelay Z} 
                                (λ l → abs (dbind l x))
                                (λ p → ax1 _ _ (dbindcong2 p x))
                                (lift-map {Z = λ _ → QDelay-map X Z} 
                                          (λ l → abs-map (dbind h ∘ l))
                                          (λ r → ax1-map _ _ (λ y₁ → dbindcong1 h (r y₁))) 
                                          (abs-map l))
                       ≅⟨ cong
                            (lift-map {Z = λ _ → QDelay Z} (λ l₁ → abs (dbind l₁ x))
                             (λ p → ax1 _ _ (dbindcong2 p x)))
                            (ax3-map {Z = λ _ → QDelay-map X Z} (λ l₁ → abs-map (dbind h ∘ l₁))
                               (λ r → ax1-map _ _ (λ y₁ → dbindcong1 h (r y₁))) l) ⟩
                       lift-map {Z = λ _ → QDelay Z} 
                                (λ l → abs (dbind l x))
                                (λ p → ax1 _ _ (dbindcong2 p x))
                                (abs-map (dbind h ∘ l))
                       ≅⟨ ax3-map {Z = λ _ → QDelay Z} (λ l₁ → abs (dbind l₁ x))
                            (λ p → ax1 _ _ (dbindcong2 p x)) (dbind h ∘ l) ⟩
                       abs (dbind (dbind h ∘ l) x)
                       ≅⟨ sym
                            (ax3-map {Z = λ _ → QDelay Z} (λ l₁ → abs (dbind (dbind h ∘ l₁) x))
                             (λ r → ax1 _ _ (dbindcong2 (λ x₁ → dbindcong1 h (r x₁)) x)) l) ⟩
                       lift-map {Z = λ _ → QDelay Z} 
                                (λ l → abs (dbind (dbind h ∘ l) x))
                                (λ r → ax1 _ _ (dbindcong2 (λ x₁ → dbindcong1 h (r x₁)) x)) 
                                (abs-map l)
                       ∎) 
                     (λ r → fixtypes'' (cong
                                          (lift-map {Z = λ _ → QDelay Z} (λ l → abs (dbind (dbind h ∘ l) x))
                                           (λ r₁ → ax1 _ _ (dbindcong2 (λ x₁ → dbindcong1 h (r₁ x₁)) x)))
                                          (ax1-map _ _ r))) 
                     (~→map~ f) ⟩
                lift-map {Z = λ _ → QDelay Z}
                         (λ l → abs (dbind (dbind h ∘ l) x))
                         (λ r → ax1 _ _ (dbindcong2 (λ x₁ → dbindcong1 h (r x₁)) x))
                         (~→map~ f)
                ≅⟨ sym (lift₂→lift (quot (Y → Delay Z) (EqR→ ≈EqR))
                                   (quot (X → Delay Y) (EqR→ ≈EqR))
                                   (λ h l → abs (dbind (dbind h ∘ l) x))
                                   (λ {h}{_}{_}{l} p r → ax1 _ _ (dbindcong2 (λ y → trans≈ (dbindcong1 h (r y)) (dbindcong2 p (l y))) x))
                                   h
                                   (~→map~ f)) ⟩
                lift₂ (quot (Y → Delay Z) (EqR→ ≈EqR))
                      (quot (X → Delay Y) (EqR→ ≈EqR))
                      (λ h l → abs (dbind (dbind h ∘ l) x))
                      (λ {h}{_}{_}{l} p r → ax1 _ _ (dbindcong2 (λ y → trans≈ (dbindcong1 h (r y)) (dbindcong2 p (l y))) x))
                      (abs-map h)
                      (~→map~ f)
                ∎) 
              (λ r → fixtypes'' (cong
                                   (λ y →
                                      lift₂ (quot (Y → Delay Z) (EqR→ ≈EqR))
                                      (quot (X → Delay Y) (EqR→ ≈EqR))
                                      (λ h l → abs (dbind (dbind h ∘ l) x))
                                      (λ {h} {_} {_} {l} p r₁ →
                                         ax1 _ _
                                         (dbindcong2
                                          (λ y₁ → trans≈ (dbindcong1 h (r₁ y₁)) (dbindcong2 p (l y₁))) x))
                                      y (~→map~ f))
                                   (ax1-map _ _ r))) 
              (~→map~ g) ⟩
         lift₂ (quot (Y → Delay Z) (EqR→ ≈EqR))
               (quot (X → Delay Y) (EqR→ ≈EqR))
               (λ h l → abs (dbind (dbind h ∘ l) x))
               (λ {h}{_}{_}{l} p r → ax1 _ _ (dbindcong2 (λ y → trans≈ (dbindcong1 h (r y)) (dbindcong2 p (l y))) x))
               (~→map~ g)
               (~→map~ f)
         ≅⟨ cong₂ {_}{_}{_}{_}{_}{_}{_}{_}
                  {λ {h}{_}{_}{l} p r → ax1 _ _ (dbindcong2 (λ y → trans≈ (dbindcong1 h (r y)) (dbindcong2 p (l y))) x)}
                  {λ {h}{_}{_}{l} p r → ax1 _ _ (trans≈ (dbindcong1 h (dbindcong2 r x)) (dbindcong2 p (dbind l x)))}
                  (λ p (r : compat₂ (quot (Y → Delay Z) (EqR→ ≈EqR)) (quot (X → Delay Y) (EqR→ ≈EqR)) p) →
                    lift₂ (quot (Y → Delay Z) (EqR→ ≈EqR)) (quot (X → Delay Y) (EqR→ ≈EqR)) p r (~→map~ g) (~→map~ f)) 
                  (ext (λ l → ext (λ h → ax1 _ _ (dlaw3 x)))) 
                  (iext (λ _ → iext (λ _ → iext (λ _ → iext (λ _ → ext (λ _ → ext (λ _ → fixtypes' (ax1 _ _ (dlaw3 x))))))))) ⟩
         lift₂ (quot (Y → Delay Z) (EqR→ ≈EqR))
               (quot (X → Delay Y) (EqR→ ≈EqR))
               (λ h l → abs (dbind h (dbind l x)))
               (λ {h}{_}{_}{l} p r → ax1 _ _ (trans≈ (dbindcong1 h (dbindcong2 r x)) (dbindcong2 p (dbind l x))))
               (~→map~ g)
               (~→map~ f)
         ≅⟨ lift-map 
              {Z = λ y → lift₂ (quot (Y → Delay Z) (EqR→ ≈EqR))
                               (quot (X → Delay Y) (EqR→ ≈EqR))
                               (λ h l → abs (dbind h (dbind l x)))
                               (λ {h}{_}{_}{l} p r → ax1 _ _ (trans≈ (dbindcong1 h (dbindcong2 r x)) (dbindcong2 p (dbind l x))))
                               (~→map~ g)
                               y ≅ 
                         qbind g (lift-map {Z = λ _ → QDelay Y}
                                 (λ h → abs (dbind h x)) 
                                 (λ p → ax1 _ _ (dbindcong2 p x))
                                 y)}
              (λ h → 
                proof
                lift₂ (quot (Y → Delay Z) (EqR→ ≈EqR))
                      (quot (X → Delay Y) (EqR→ ≈EqR))
                      (λ h l → abs (dbind h (dbind l x)))
                      (λ {h}{_}{_}{l} p r → ax1 _ _ (trans≈ (dbindcong1 h (dbindcong2 r x)) (dbindcong2 p (dbind l x))))
                      (~→map~ g)
                      (abs-map h)
                ≅⟨ lift₂→lift' (quot (Y → Delay Z) (EqR→ ≈EqR)) 
                               (quot (X → Delay Y) (EqR→ ≈EqR)) 
                               (λ h₁ l → abs (dbind h₁ (dbind l x))) 
                               (λ {h₁} {_} {_} {l} p r →
                                    ax1 _ _
                                    (trans≈ (dbindcong1 h₁ (dbindcong2 r x))
                                     (dbindcong2 p (dbind l x)))) 
                               (~→map~ g) 
                               h ⟩
                lift-map {Z = λ _ → QDelay Z}
                         (λ l → abs (dbind l (dbind h x)))
                         (λ r → ax1 _ _ (dbindcong2 r (dbind h x)))
                         (~→map~ g)
                ≅⟨ sym qbindabs ⟩
                qbind g (abs (dbind h x))
                ≅⟨ cong (qbind g) (sym (ax3-map {Z = λ _ → QDelay Y} (λ h₁ → abs (dbind h₁ x)) (λ p → ax1 _ _ (dbindcong2 p x)) h)) ⟩
                qbind g (lift-map {Z = λ _ → QDelay Y}
                                  (λ h → abs (dbind h x)) 
                                  (λ p → ax1 _ _ (dbindcong2 p x))
                                  (abs-map h))
                ∎)
              (λ r → fixtypes'' (cong
                                   (qbind g ∘
                                    lift-map {Z = λ _ → QDelay Y} (λ h → abs (dbind h x))
                                    (λ p → ax1 _ _ (dbindcong2 p x)))
                                   (ax1-map _ _ r)))
              (~→map~ f) ⟩
         qbind g (lift-map {Z = λ _ → QDelay Y}
                           (λ h → abs (dbind h x)) 
                           (λ p → ax1 _ _ (dbindcong2 p x))
                           (~→map~ f))
         ≅⟨ cong (qbind g) (sym qbindabs) ⟩
         qbind g (qbind f (abs x))
         ∎)
       (λ r → fixtypes'' (cong (qbind g ∘ qbind f) (ax1 _ _ r))) 
       q)

DelayM : Monad Sets
DelayM = record { 
  T    = QDelay; 
  η    = abs ∘ now;
  bind = qbind;
  law1 = qlaw1 ;
  law2 = qlaw2;
  law3 = qlaw3 }


dmap : ∀{X Y} → (X → Y) → Delay X → Delay Y
dmap f = dbind (now ∘ f) --rep (Fun.HMap (TFun DelayM) f (abs x))

qmap : ∀{X Y} → (X → Y) → QDelay X → QDelay Y
qmap f = qbind (abs ∘ now ∘ f)

str : ∀{X Y} → X × Delay Y → Delay (X × Y)
str (x , dy) = dmap (λ y → (x , y)) dy

qstr : ∀{X Y} → X × QDelay Y → QDelay (X × Y)
qstr (x , dy) = qmap (λ y → x , y) dy

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
-}

-- axiom of delayed choice

left' : {X : Set} → Delay X → Stream (X ⊎ ⊤)
left' (now x)   = repeat (inj₁ x)
hd (left' (later x)) = inj₂ _
tl (left' (later x)) = left' (force x)

mutual
  right' : {X : Set} → Stream (X ⊎ ⊤) → Delay X
  right' xs with hd xs
  right' xs | inj₁ x = now x
  right' xs | inj₂ _ = later (∞right' (tl xs))

  ∞right' : {X : Set} → Stream (X ⊎ ⊤) → ∞Delay X
  force (∞right' xs) = right' xs

open import AComega

lem : {X : Set} → ∥ X ∥ ⊎ ⊤ → ∥ X ⊎ ⊤ ∥
lem {X} (inj₁ x) = liftX (λ _ → ∥ X ⊎ ⊤ ∥) (absX ∘ inj₁) (λ _ → soundX _) x
  where open Quotient (quot X (Triv X))
          renaming (lift to liftX)
        open Quotient (quot (X ⊎ ⊤) (Triv (X ⊎ ⊤)))
          renaming (abs to absX; sound to soundX)
lem {X} (inj₂ y) = absX (inj₂ y)
  where open Quotient (quot (X ⊎ ⊤) (Triv (X ⊎ ⊤)))
          renaming (lift to liftX; abs to absX)

ACD : {X : Set} → Delay ∥ X ∥ → ∥ Delay X ∥
ACD dx = map∥ right' (acco (smap lem  (left' dx)))
