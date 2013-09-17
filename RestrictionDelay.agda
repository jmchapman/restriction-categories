
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
open Monad DelayM
open Cat (Kl DelayM)

drest : ∀{X Y} → (X → Delay Y) → X → Delay X
drest f x = map proj₁ (str (x , f x))

{-
-- A lemma we need for R4

funcong∼ : ∀{X Y}(dx : Delay X)(f g : X → Delay Y) → ((x : X) → f x ∼ g x) → 
           dbind f dx ∼ dbind g dx
funcong∼ (now x) f g p = p x
funcong∼ (later dx) f g p = later∼ (♯ (funcong∼ (♭ dx) f g p))

dbind↓2' : ∀{Y Z}{z : Y}{dy dz : Delay Y}{g : Y → Delay Z} → 
           dbind (λ y → dbind (λ _ → dy) (g y)) dy ∼ dz → dz ↓ z →
           dbind (λ y → dbind (λ _ → now y) (g y)) dy ↓ z
dbind↓2' {Y}{Z}{z}{now x} p q = ≈↓ (∼→≈ (sym∼ p)) q
dbind↓2' {Y}{Z}{z}{later dy}{later dz}{g} (later∼ p) (later↓ q) with ♭ dz
... | a with 
  trans∼ 
    (sym∼ (dbindlater (♭ dy)))
    (trans∼
      (funcong∼ (♭ dy) 
                (λ y → later (♯ dbind (λ _ → ♭ dy) (g y))) 
                _
                (λ y → trans∼ (later∼ (♯ refl∼)) (sym∼ (dbindlater (g y)))))
      (♭ p))
dbind↓2' {Y}{Z}{z}{later dy}{later dz}{g} (later∼ p) (later↓ (later↓ q)) | 
  .(later dy') | 
  later∼ {._} {dy'} r = later↓ (dbind↓2' {dy = ♭ dy}{g = g} (♭ r) q)
 
dbind↓2 : ∀{Y Z}{z : Y}{dy : Delay Y}{g : Y → Delay Z} → 
          dbind (λ y → dbind (λ _ → dy) (g y)) dy ↓ z →
          dbind (λ y → dbind (λ _ → now y) (g y)) dy ↓ z
dbind↓2 {dy = dy}{g = g} p = dbind↓2' {dy = dy}{g = g} refl∼ p

lemma3' : ∀{Y Z}{dy dz : Delay Y}{g : Y → Delay Z} → 
          dbind (λ y → dbind (λ _ → dy) (g y)) dy ≈ dz → 
          dbind (λ y → dbind (λ _ → now y) (g y)) dy ≈ dz
lemma3' {Y}{Z}{now y} p = p
lemma3' {Y}{Z}{later dy}{dz}{g} (↓≈ (later↓ p) q) with
  ≈↓ 
    (sym≈
      (∼→≈ 
        (funcong∼ (♭ dy) 
                  (λ y → later (♯ dbind (λ _ → ♭ dy) (g y))) 
                  _
                  (λ y → (trans∼ (later∼ (♯ refl∼))
                         (sym∼ (dbindlater {_} {_} {λ _ → dy} (g y))))))))
    p
... | r with
  ≈↓ (sym≈
        (trans≈ (trans≈ laterlem (later≈ (♯ refl≈)))
         (∼→≈ (sym∼ (dbindlater (♭ dy)))))) r
... | r' = ↓≈ (later↓ (dbind↓2 {dy = ♭ dy}{g = g} r')) q 
lemma3' {Y}{Z}{later dy}{later dz}{g} (later≈ p)
  with 
  trans≈
    (∼→≈ 
      (funcong∼ (♭ dy)
                (λ y → later (♯ dbind (λ _ → ♭ dy) (g y))) 
                _ 
                (λ y → (trans∼ (later∼ (♯ refl∼)) (sym∼ (dbindlater (g y)))))))
    (♭ p)
... | r =
  later≈ 
    (♯ lemma3' {dy = ♭ dy} 
               {dz = ♭ dz}
               {g = g}
               (trans≈ (trans≈ laterlem 
                               (later≈ (♯ refl≈))) 
                       (trans≈ (∼→≈ (sym∼ (dbindlater (♭ dy)))) 
                               r)))
lemma3 : ∀{Y Z}{dy : Delay Y}{g : Y → Delay Z} → 
         dbind (λ y → dbind (λ _ → now y) (g y)) dy ≈ 
         dbind (λ y → dbind (λ _ → dy) (g y)) dy
lemma3 {Y}{Z}{dy}{g} = lemma3' {Y}{Z}{dy}{_}{g} refl≈

-- The Kleisli category of the Delay monad is a restriction category

drest≅ : ∀{X Y}(x : X)(f : X → Delay Y) → drest f x ≅ dbind (λ z → now x) (f x)
drest≅ x f = cong (λ f' → f' (f x)) (sym law3) 

compdrest : ∀{X Y Z}{f : Z → Delay X}{g : Z → Delay Y}(z : Z) → 
            dbind (λ _ → f z) (g z) ≅ dbind f (dbind (λ a → now z) (g z))
compdrest {X}{Y}{Z}{f}{g} z = 
  proof
  dbind (λ _ → f z) (g z) 
  ≅⟨ cong (λ f' → f' (g z)) law3 ⟩
  dbind f (dbind (λ a → now z) (g z))
  ∎

dR1 : ∀{X Y}{f : X → Delay Y}(x : X) → dbind f (drest f x) ≅ f x
dR1 {f = f} x = 
  proof
  dbind f (drest f x)
  ≅⟨ cong (dbind f) (drest≅ x f) ⟩
  dbind f (dbind (λ z → now x) (f x))
  ≅⟨ sym (compdrest {f = f} {g = f} x) ⟩
  dbind (λ _ → f x) (f x)
  ≅⟨ quotient (sym≈ (dcomp≈dbind {_}{_}{f x})) ⟩
  dcomp (f x) (f x)
  ≅⟨ quotient (dcomp≈fst refl≈) ⟩
  f x 
  ∎

dR2 : ∀{X Y Z}{f : X → Delay Y}{g : X → Delay Z}(x : X) → 
      dbind (drest f) (drest g x) ≅ dbind (drest g) (drest f x)
dR2 {f = f}{g = g} x =
  proof 
  dbind (drest f) (drest g x)
  ≅⟨ cong (dbind (drest f)) (drest≅ x g) ⟩ 
  dbind (drest f) (dbind (λ z → now x) (g x))
  ≅⟨ sym (compdrest {f = drest f} {g = g} x) ⟩ 
  dbind (λ _ → drest f x) (g x)
  ≅⟨ cong (λ y → dbind (λ _ → y) (g x)) (drest≅ x f) ⟩
  dbind (λ _ → dbind (λ _ → now x) (f x)) (g x)
  ≅⟨ cong (λ y → dbind (λ _ → y) (g x)) 
          (quotient (sym≈ (dcomp≈dbind {_}{_}{f x}))) ⟩
  dbind (λ _ → dcomp (f x) (now x)) (g x)
  ≅⟨ quotient (sym≈ (dcomp≈dbind {_}{_}{g x})) ⟩
  dcomp (g x) (dcomp (f x) (now x))
  ≅⟨ quotient (∼→≈ (dcompcomm {_}{_}{_}{g x}{f x})) ⟩
  dcomp (f x) (dcomp (g x) (now x))
  ≅⟨ quotient (dcomp≈dbind {_}{_}{f x}) ⟩
  dbind (λ _ → dcomp (g x) (now x)) (f x)
  ≅⟨ cong (λ y → dbind (λ _ → y) (f x)) (quotient (dcomp≈dbind {_}{_}{g x})) ⟩
  dbind (λ _ → (dbind (λ _ → now x) (g x))) (f x)
  ≅⟨ cong (λ y → dbind (λ _ → y) (f x)) (sym (drest≅ x g)) ⟩
  dbind (λ _ → drest g x) (f x)
  ≅⟨ compdrest {f = drest g} {g = f} x ⟩ 
  dbind (drest g) (dbind (λ z → now x) (f x))
  ≅⟨ cong (dbind (drest g)) (sym (drest≅ x f)) ⟩ 
  dbind (drest g) (drest f x)
  ∎

dR3 : ∀{X Y Z}{f : X → Delay Y}{g : X → Delay Z}(x : X) → 
    dbind (drest g) (drest f x) ≅ drest (dbind g ∘ (drest f)) x
dR3 {f = f}{g = g} x = 
  proof
  dbind (drest g) (drest f x)
  ≅⟨ cong (dbind (drest g)) (drest≅ x f) ⟩
  dbind (drest g) (dbind (λ z → now x) (f x))
  ≅⟨ sym (compdrest {f = drest g} {g = f} x) ⟩
  dbind (λ _ → drest g x) (f x)
  ≅⟨ cong (λ y → dbind (λ _ → y) (f x)) (drest≅ x g) ⟩ 
  dbind (λ _ → dbind (λ z → now x) (g x)) (f x)
  ≅⟨ cong (λ f' → f' (f x)) law3 ⟩ 
  dbind (λ z → now x) (dbind (λ _ → g x) (f x))
  ≅⟨ cong (dbind (λ z → now x)) (compdrest {f = g} {g = f} x) ⟩ 
  dbind (λ z → now x) (dbind g (dbind (λ z → now x) (f x)))
  ≅⟨ cong (dbind (λ z → now x) ∘ dbind g) (sym (drest≅ x f)) ⟩ 
  dbind (λ z → now x) (dbind g (drest f x))
  ≅⟨ sym (drest≅ x (dbind g ∘ drest f)) ⟩ 
  drest (dbind g ∘ (drest f)) x
  ∎

dR4 : ∀{X Y Z}{f : X → Delay Y}{g : Y → Delay Z}(x : X) →
      dbind (drest g) (f x) ≅ dbind f (drest (dbind g ∘ f) x)
dR4 {X}{Y}{Z}{f = f}{g = g} x = 
  proof
  dbind (λ y → drest g y) (f x)
  ≅⟨ cong (λ t → dbind t (f x)) (ext (λ y → drest≅ y g)) ⟩
  dbind (λ y → dbind (λ _ → now y) (g y)) (f x)
  ≅⟨ quotient (lemma3 {dy = f x} {g = g}) ⟩
  dbind (λ y → dbind (λ _ → f x) (g y)) (f x)
  ≅⟨ cong (λ h → h (f x)) law3 ⟩
  dbind (λ _ → f x) (dbind g (f x))
  ≅⟨ compdrest {f = f} {g = dbind g ∘ f} x ⟩
  dbind f (dbind (λ z → now x) (dbind g (f x)))
  ≅⟨ cong (dbind f) (sym (drest≅ x (dbind g ∘ f))) ⟩
  dbind f (drest (dbind g ∘ f) x)
  ∎

DelayR : RestCat
DelayR = record { 
  cat  = Kl DelayM; 
  rest = drest; 
  R1   = λ {_}{_}{f} → ext (dR1 {f = f});
  R2   = λ {_}{_}{_}{f}{g} → ext (dR2 {f = f} {g = g}); 
  R3   = λ {_}{_}{_}{f}{g} → ext (dR3 {f = f} {g = g}); 
  R4   = λ {_}{_}{_}{f}{g} → ext (dR4 {f = f} {g = g})}

open RestCat DelayR

-- Restriction product

open import RestrictionProducts DelayR
open import Totals DelayR
open Tot

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

-- Meets

open import Order DelayR
open Meets
open import Relation.Binary
open import Relation.Nullary.Core

dMt1-aux  : ∀{X}{_≟_ : Decidable {A = X} _≅'_}(dx : Delay X) → 
            dmeet-aux {X}{_≟_} dx dx ≈ dx
dMt1-aux {X}{_≟_} (now x) with x ≟ x
dMt1-aux (now x) | yes refl = ↓≈ now↓ now↓
dMt1-aux (now x) | no ¬p with ¬p refl
dMt1-aux (now x) | no ¬p | ()
dMt1-aux (later dx) = later≈ (♯ (dMt1-aux (♭ dx)))

dMt1  : ∀{X Y}{_≟_ : Decidable {A = Y}{B = Y} _≅'_}{f : X → Delay Y} → 
        (x : X) → dmeet {X}{Y}{_≟_} f f x ≅ f x
dMt1 {f = f} x = quotient (dMt1-aux (f x))

dMt2a-aux' : ∀{X}{_≟_ : Decidable {A = X} _≅'_}{dx dy : Delay X} →
             dmeet-aux {X}{_≟_} dx dy ≈ 
             dcomp (dmeet-aux {X}{_≟_} dx dy) dy
dMt2a-aux' {X}{_≟_}{now x}{now y} with x ≟ y
dMt2a-aux' {X}{_≟_}{now x}{now .x} | yes refl = ↓≈ now↓ now↓
dMt2a-aux' {X}{_≟_}{now x}{now y} | no ¬p = 
  later≈ (♯ dMt2a-aux' {_}{_}{now x}{now y})
dMt2a-aux' {X}{_≟_}{later dx}{now y} = later≈ (♯ dMt2a-aux' {_}{_}{♭ dx})
dMt2a-aux' {X} {_≟_}{now x}{later dy} = 
  later≈ (♯ dMt2a-aux' {_}{_}{now x}{♭ dy})
dMt2a-aux' {X} {_≟_}{later dx}{later dy} = 
  later≈ (♯ dMt2a-aux' {_}{_}{♭ dx}{♭ dy})

dMt2a-aux : ∀{X}{_≟_ : Decidable {A = X} _≅'_}{dx dy : Delay X} →
            dmeet-aux {X}{_≟_} dx dy ≈ 
            dbind (λ _ → dy) (dmeet-aux {X}{_≟_} dx dy)
dMt2a-aux {X}{_≟_}{dx}{dy} = 
  trans≈ (dMt2a-aux' {_}{_}{dx}{dy}) 
         (dcomp≈dbind {_}{_}{dmeet-aux {_}{_≟_} dx dy})

dMt2a : ∀{X Y}{_≟_ : Decidable {A = Y}{B = Y} _≅'_}{f g : X → Delay Y} →
        dmeet {X}{Y}{_≟_} f g ≤ g
dMt2a {X}{Y}{_≟_}{f}{g} = ext (λ x → 
  proof 
  dbind g (drest (dmeet f g) x)
  ≅⟨ cong (dbind g) (drest≅ x (dmeet f g)) ⟩
  dbind g (dbind (λ z → now x) (dmeet f g x))
  ≅⟨ sym (compdrest {f = g}{g = dmeet f g} x) ⟩
  dbind (λ _ → g x) (dmeet f g x)
  ≅⟨ quotient (sym≈ (dMt2a-aux {dx = f x}{dy = g x})) ⟩
  dmeet f g x
  ∎)

-- dMt2b is similar

-- Joins

_d⌣_ : ∀{X Y}(f g : X → Delay Y) → Set
_d⌣_ {X} f g = {x : X} → dcomp (f x) (g x) ≈ dcomp (g x) (f x)

djoin-aux : ∀{X}(dx dy : Delay X) → dcomp dx dy ≈ dcomp dy dx → Delay X
djoin-aux (now x) (now .x) (↓≈ now↓ now↓) = now x
djoin-aux (now x) (later dy) p = now x
djoin-aux (later dx) (now y) p = now y
djoin-aux (later dx) (later dy) (↓≈ (later↓ {y = y} p) (later↓ q)) = now y
djoin-aux (later dx) (later dy) (later≈ p) = 
  later (♯ (djoin-aux (♭ dx) (♭ dy) (♭ p)))

djoin : {X Y : Set}(f g : X → Delay Y) → f d⌣ g → X → Delay Y
djoin f g p x = djoin-aux (f x) (g x) p

dJn1a-aux : ∀{X}{dx dy : Delay X}{p : dcomp dx dy ≈ dcomp dy dx} →
            dcomp dx (djoin-aux dx dy p) ∼ dx
dJn1a-aux {X}{now x}{now .x}{↓≈ now↓ now↓} = now∼
dJn1a-aux {X}{now x}{later dy} = now∼
dJn1a-aux {X} {later dx} {now y} {↓≈ (later↓ p) (later↓ q)} = 
  later∼ (♯ (dcomp≈→∼ (↓≈ p q)))
dJn1a-aux {X} {later dx} {now y} {later≈ p} = 
  later∼ (♯ dcomp≈→∼ (♭ p))
dJn1a-aux {X} {later dx} {later dy} {↓≈ (later↓ p) (later↓ q)} = 
  later∼ (♯ dcomp≈→∼ (dcomp≈fst (↓≈ (dcomp↓snd {_}{_}{♭ dy} q) now↓)))
dJn1a-aux {X} {later dx} {later dy} {later≈ p} = 
  later∼ (♯ dJn1a-aux {_}{♭ dx}{♭ dy}{♭ p})

dJn1a : ∀{X Y}{f g : X → Delay Y}{p : f d⌣ g} → f ≤ djoin f g p
dJn1a {f = f}{g = g}{p = p} = ext (λ x → 
  proof
  dbind (djoin f g p) (drest f x)
  ≅⟨ cong (dbind (djoin f g p)) (drest≅ x f) ⟩
  dbind (djoin f g p) (dbind (λ _ → now x) (f x))
  ≅⟨ sym (compdrest {f = djoin f g p} {g = f} x) ⟩
  dbind (λ _ → djoin f g p x) (f x)
  ≅⟨ quotient (sym≈ (dcomp≈dbind {_}{_}{f x})) ⟩
  dcomp (f x) (djoin f g p x)
  ≅⟨ quotient (∼→≈ (dJn1a-aux {_} {f x} {g x} {p})) ⟩
  f x
  ∎)
-}

-- Independence (also called disjointness)

data _d⊥_  {X Y : Set} : Delay X → Delay Y → Set where
  now⊥later   : ∀{x dy} → ∞ (now x d⊥ (♭ dy)) → now x d⊥ later dy
  later⊥now   : ∀{dx y} → ∞ ((♭ dx) d⊥ now y) → later dx d⊥ now y
  later⊥later : ∀{dx dy} → ∞ ((♭ dx) d⊥ (♭ dy)) → later dx d⊥ later dy

_⊥_ : ∀{X Y} → (X → Delay X) → (X → Delay Y) → Set
f ⊥ g = ∀ x → f x d⊥ g x

-- Iteration

d† : ∀{X Y} → (X → Delay X) → Delay X → Delay Y → Delay Y
d† f (now x) dy = later (♯ (d† f (f x) dy))
d† f (later dx) (now y) = now y
d† f (later dx) (later dy) = later (♯ (d† f (♭ dx) (♭ dy)))

_†_ : ∀{X Y} → (X → Delay X) → (X → Delay Y) → X → Delay Y
(f † g) x = d† f (f x) (g x)






















{-

-- Old (impossible to work with) approach

-- Some lemmata we need

dbind↓' : ∀{X}{dx dz : Delay X}{y : X} → dbind (λ _ → dx) dx ∼ dz → dz ↓ y → 
          dx ↓ y
dbind↓' {X}{now x} now∼ q = q
dbind↓' {X}{later dx}{later dz} (later∼ p) (later↓ q) with 
  ♭ dz |
  trans∼ (sym∼ (dbindlater (♭ dx))) (♭ p)
dbind↓' {X} {later dx} {later dz} (later∼ p) (later↓ (later↓ q)) | 
  .(later dy) | 
  later∼ {._}{dy} r = 
  later↓ (dbind↓' (♭ r) q)

dbind↓ : ∀{X}{dx : Delay X}{y : X} → dbind (λ _ → dx) dx ↓ y → dx ↓ y
dbind↓ = dbind↓' refl∼

lemma' : ∀{X}{dx dz : Delay X} → dbind (λ _ → dx) dx ≈ dz → dx ≈ dz
lemma' {X} {now x} p = p
lemma' {X} {later dx} (↓≈ (later↓ p) q) = 
  ↓≈ 
    (later↓ 
      (dbind↓ 
        (≈↓ 
          (trans≈ 
            (∼→≈ (trans∼ (dbindlater (♭ dx)) 
                         (later∼ (♯ refl∼)))) 
            (sym≈ laterlem)) 
          p))) 
    q
lemma' {X} {later dx}{later dz} (later≈ p) = 
  later≈ (♯ 
    (lemma' 
      (trans≈
        (trans≈
          (trans≈ 
            (laterlem {_} {dbind (λ _ → ♭ dx) (♭ dx)})
            (later≈ (♯ refl≈)))
          (sym≈ (∼→≈ (dbindlater (♭ dx)))))
        (♭ p))))

lemma : ∀{X}{dx : Delay X} → dx ≈ dbind (λ _ → dx) dx
lemma = lemma' refl≈

lemma2' : ∀{X Y Z}{x : X}{dy : Delay Y}{dz : Delay Z}{dx : Delay X} → 
          dbind (λ _ → dbind (λ _ → now x) dz) dy ∼ dx →
          dbind (λ _ → dbind (λ _ → now x) dy) dz ∼ dx 
lemma2' {X}{Y}{Z}{x}{dy}{now z}{dx} p = p
lemma2' {X}{Y}{Z}{x}{dy}{later dz}{dx} p with trans∼ (sym∼ (dbindlater dy)) p
lemma2' {X}{Y}{Z}{x}{dy}{later dz}{later dx} p | later∼ q = 
  later∼ (♯ (lemma2' {_}{_}{_}{_}{dy}{♭ dz}{♭ dx} (♭ q)))

lemma2 : ∀{X Y Z}{x : X}{dy : Delay Y}{dz : Delay Z} → 
         dbind (λ _ → dbind (λ _ → now x) dy) dz ∼ 
         dbind (λ _ → dbind (λ _ → now x) dz) dy
lemma2 {X}{Y}{Z}{x}{dy}{dz} = lemma2' {X}{Y}{Z}{x}{dy}{dz}{_} refl∼

funcong∼ : ∀{X Y}(dx : Delay X)(f g : X → Delay Y) → ((x : X) → f x ∼ g x) → 
           dbind f dx ∼ dbind g dx
funcong∼ (now x) f g p = p x
funcong∼ (later dx) f g p = later∼ (♯ (funcong∼ (♭ dx) f g p))

dbind↓2' : ∀{Y Z}{z : Y}{dy dz : Delay Y}{g : Y → Delay Z} → 
           dbind (λ y → dbind (λ _ → dy) (g y)) dy ∼ dz → dz ↓ z →
           dbind (λ y → dbind (λ _ → now y) (g y)) dy ↓ z
dbind↓2' {Y}{Z}{z}{now x} p q = ≈↓ (∼→≈ (sym∼ p)) q
dbind↓2' {Y}{Z}{z}{later dy}{later dz}{g} (later∼ p) (later↓ q) with ♭ dz
... | a with 
  trans∼ 
    (sym∼ (dbindlater (♭ dy)))
    (trans∼
      (funcong∼ (♭ dy) 
                (λ y → later (♯ dbind (λ _ → ♭ dy) (g y))) 
                _
                (λ y → trans∼ (later∼ (♯ refl∼)) (sym∼ (dbindlater (g y)))))
      (♭ p))
dbind↓2' {Y}{Z}{z}{later dy}{later dz}{g} (later∼ p) (later↓ (later↓ q)) | 
  .(later dy') | 
  later∼ {._} {dy'} r = later↓ (dbind↓2' {dy = ♭ dy}{g = g} (♭ r) q)
 
dbind↓2 : ∀{Y Z}{z : Y}{dy : Delay Y}{g : Y → Delay Z} → 
          dbind (λ y → dbind (λ _ → dy) (g y)) dy ↓ z →
          dbind (λ y → dbind (λ _ → now y) (g y)) dy ↓ z
dbind↓2 {dy = dy}{g = g} p = dbind↓2' {dy = dy}{g = g} refl∼ p

lemma3' : ∀{Y Z}{dy dz : Delay Y}{g : Y → Delay Z} → 
          dbind (λ y → dbind (λ _ → dy) (g y)) dy ≈ dz → 
          dbind (λ y → dbind (λ _ → now y) (g y)) dy ≈ dz
lemma3' {Y}{Z}{now y} p = p
lemma3' {Y}{Z}{later dy}{dz}{g} (↓≈ (later↓ p) q) with
  ≈↓ 
    (sym≈
      (∼→≈ 
        (funcong∼ (♭ dy) 
                  (λ y → later (♯ dbind (λ _ → ♭ dy) (g y))) 
                  _
                  (λ y → (trans∼ (later∼ (♯ refl∼))
                         (sym∼ (dbindlater {_} {_} {λ _ → dy} (g y))))))))
    p
... | r with
  ≈↓ (sym≈
        (trans≈ (trans≈ laterlem (later≈ (♯ refl≈)))
         (∼→≈ (sym∼ (dbindlater (♭ dy)))))) r
... | r' = ↓≈ (later↓ (dbind↓2 {dy = ♭ dy}{g = g} r')) q 
lemma3' {Y}{Z}{later dy}{later dz}{g} (later≈ p)
  with 
  trans≈
    (∼→≈ 
      (funcong∼ (♭ dy)
                (λ y → later (♯ dbind (λ _ → ♭ dy) (g y))) 
                _ 
                (λ y → (trans∼ (later∼ (♯ refl∼)) (sym∼ (dbindlater (g y)))))))
    (♭ p)
... | r =
  later≈ 
    (♯ lemma3' {dy = ♭ dy} 
               {dz = ♭ dz}
               {g = g}
               (trans≈ (trans≈ laterlem 
                               (later≈ (♯ refl≈))) 
                       (trans≈ (∼→≈ (sym∼ (dbindlater (♭ dy)))) 
                               r)))

lemma3 : ∀{Y Z}{dy : Delay Y}{g : Y → Delay Z} → 
         dbind (λ y → dbind (λ _ → now y) (g y)) dy ≈ 
         dbind (λ y → dbind (λ _ → dy) (g y)) dy
lemma3 {Y}{Z}{dy}{g} = lemma3' {Y}{Z}{dy}{_}{g} refl≈

-- The Kleisli category of the Delay monad is a restriction category

drest≅ : ∀{X Y}(x : X)(f : X → Delay Y) → drest f x ≅ dbind (λ z → now x) (f x)
drest≅ x f = cong (λ f' → f' (f x)) (sym law3) 

compdrest : ∀{X Y Z}{f : Z → Delay X}{g : Z → Delay Y}(z : Z) → 
            dbind (λ _ → f z) (g z) ≅ dbind f (dbind (λ a → now z) (g z))
compdrest {X}{Y}{Z}{f}{g} z = 
  proof
  dbind (λ _ → f z) (g z) 
  ≅⟨ cong (λ f' → f' (g z)) law3 ⟩
  dbind f (dbind (λ a → now z) (g z))
  ∎

dR1 : ∀{X Y}{f : X → Delay Y}(x : X) → dbind f (drest f x) ≅ f x
dR1 {f = f} x = 
  proof
  dbind f (drest f x)
  ≅⟨ cong (dbind f) (drest≅ x f) ⟩
  dbind f (dbind (λ z → now x) (f x))
  ≅⟨ sym (compdrest {f = f} {g = f} x) ⟩
  dbind (λ _ → f x) (f x)
  ≅⟨ quotient (sym≈ (lemma {_} {f x})) ⟩
  f x 
  ∎

dR2 : ∀{X Y Z}{f : X → Delay Y}{g : X → Delay Z}(x : X) → 
      dbind (drest f) (drest g x) ≅ dbind (drest g) (drest f x)
dR2 {f = f}{g = g} x =
  proof 
  dbind (drest f) (drest g x)
  ≅⟨ cong (dbind (drest f)) (drest≅ x g) ⟩ 
  dbind (drest f) (dbind (λ z → now x) (g x))
  ≅⟨ sym (compdrest {f = drest f} {g = g} x) ⟩ 
  dbind (λ _ → drest f x) (g x)
  ≅⟨ cong (λ y → dbind (λ _ → y) (g x)) (drest≅ x f) ⟩
  dbind (λ _ → (dbind (λ _ → now x) (f x))) (g x)
  ≅⟨ quotient (∼→≈ (lemma2 {dy = f x}{dz = g x})) ⟩ 
  dbind (λ _ → (dbind (λ _ → now x) (g x))) (f x)
  ≅⟨ cong (λ y → dbind (λ _ → y) (f x)) (sym (drest≅ x g)) ⟩
  dbind (λ _ → drest g x) (f x)
  ≅⟨ compdrest {f = drest g} {g = f} x ⟩ 
  dbind (drest g) (dbind (λ z → now x) (f x))
  ≅⟨ cong (dbind (drest g)) (sym (drest≅ x f)) ⟩ 
  dbind (drest g) (drest f x)
  ∎

dR3 : ∀{X Y Z}{f : X → Delay Y}{g : X → Delay Z}(x : X) → 
    dbind (drest g) (drest f x) ≅ drest (dbind g ∘ (drest f)) x
dR3 {f = f}{g = g} x = 
  proof
  dbind (drest g) (drest f x)
  ≅⟨ cong (dbind (drest g)) (drest≅ x f) ⟩
  dbind (drest g) (dbind (λ z → now x) (f x))
  ≅⟨ sym (compdrest {f = drest g} {g = f} x) ⟩
  dbind (λ _ → drest g x) (f x)
  ≅⟨ cong (λ y → dbind (λ _ → y) (f x)) (drest≅ x g) ⟩ 
  dbind (λ _ → dbind (λ z → now x) (g x)) (f x)
  ≅⟨ cong (λ f' → f' (f x)) law3 ⟩ 
  dbind (λ z → now x) (dbind (λ _ → g x) (f x))
  ≅⟨ cong (dbind (λ z → now x)) (compdrest {f = g} {g = f} x) ⟩ 
  dbind (λ z → now x) (dbind g (dbind (λ z → now x) (f x)))
  ≅⟨ cong (dbind (λ z → now x) ∘ dbind g) (sym (drest≅ x f)) ⟩ 
  dbind (λ z → now x) (dbind g (drest f x))
  ≅⟨ sym (drest≅ x (dbind g ∘ drest f)) ⟩ 
  drest (dbind g ∘ (drest f)) x
  ∎

dR4 : ∀{X Y Z}{f : X → Delay Y}{g : Y → Delay Z}(x : X) →
      dbind (drest g) (f x) ≅ dbind f (drest (dbind g ∘ f) x)
dR4 {X}{Y}{Z}{f = f}{g = g} x = 
  proof
  dbind (λ y → drest g y) (f x)
  ≅⟨ cong (λ t → dbind t (f x)) (ext (λ y → drest≅ y g)) ⟩
  dbind (λ y → dbind (λ z → now y) (g y)) (f x)
  ≅⟨ quotient (lemma3 {dy = f x} {g = g}) ⟩
  dbind (λ y → dbind (λ _ → f x) (g y)) (f x)
  ≅⟨ cong (λ h → h (f x)) law3 ⟩
  dbind (λ _ → f x) (dbind g (f x))
  ≅⟨ compdrest {f = f} {g = dbind g ∘ f} x ⟩
  dbind f (dbind (λ z → now x) (dbind g (f x)))
  ≅⟨ cong (dbind f) (sym (drest≅ x (dbind g ∘ f))) ⟩
  dbind f (drest (dbind g ∘ f) x)
  ∎

DelayR : RestCat
DelayR = record { 
  cat  = Kl DelayM; 
  rest = drest; 
  R1   = λ {_}{_}{f} → ext (dR1 {f = f});
  R2   = λ {_}{_}{_}{f}{g} → ext (dR2 {f = f} {g = g}); 
  R3   = λ {_}{_}{_}{f}{g} → ext (dR3 {f = f} {g = g}); 
  R4   = λ {_}{_}{_}{f}{g} → ext (dR4 {f = f} {g = g})}

open RestCat DelayR

{-
-- Restriction product

open import RestrictionProducts DelayR
open import Totals DelayR
open Tot

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

{-
dbind-dproj₁-nowy : ∀{X Y}{y : Y}(dx : Delay X) → 
                   dbind (hom dp₁) d⟨ dx , now y ⟩-aux ∼ dx
dbind-dproj₁-nowy (now x) = refl∼
dbind-dproj₁-nowy (later dx) = later∼ (♯ dbind-dproj₁-nowy (♭ dx))

dbind-dproj₁-nowx : ∀{X Y}{x : X}(dy : Delay Y) → 
                    dbind (hom dp₁) d⟨ now x , dy ⟩-aux ∼ dbind (λ _ → now x) dy
dbind-dproj₁-nowx (now y) = now∼
dbind-dproj₁-nowx (later dy) = later∼ (♯ (dbind-dproj₁-nowx (♭ dy)))

dbind-dproj₂-nowx : ∀{X Y}{x : X}(dy : Delay Y) → 
                   dbind (hom dp₂) d⟨ now x , dy ⟩-aux ∼ dy
dbind-dproj₂-nowx (now y) = refl∼
dbind-dproj₂-nowx (later dy) = later∼ (♯ dbind-dproj₂-nowx (♭ dy))

dbind-dproj₂-nowy : ∀{X Y}{y :  Y}(dx : Delay X) → 
             dbind (hom dp₂) d⟨ dx , now y ⟩-aux ∼ dbind (λ _ → now y) dx
dbind-dproj₂-nowy (now x) = now∼
dbind-dproj₂-nowy (later dx) = later∼ (♯ (dbind-dproj₂-nowy (♭ dx)))
-}

{-
dtr1-aux : ∀{X Y}(dx : Delay X)(dy : Delay Y) → 
           dbind (hom dp₁) d⟨ dx , dy ⟩-aux ≈ dbind (λ _ → dx) dy
dtr1-aux (now x) (now y) = refl≈
dtr1-aux (now x) (later dy) = later≈ (♯ dtr1-aux (now x) (♭ dy) )
dtr1-aux (later dx) (now y) = later≈ (♯ ∼→≈ (dbind-dproj₁-nowy (♭ dx)))
dtr1-aux (later dx) (later dy) = later≈ (♯ {!!})

--trans≈ (dtr1-aux (♭ dx) (♭ dy)) (trans≈ laterlem (trans≈ (later≈ (♯ refl≈)) (sym≈ (∼→≈ (dbindlater (♭ dy))))))
-}

-- First triangle commutes

dtr1-aux↓' : ∀{X Y}{z : X}(dx dz : Delay X)(dy : Delay Y) →
             dbind (λ _ → dx) dy ∼ dz → dz ↓ z → 
             dbind (hom dp₁) d⟨ dx , dy ⟩-aux ↓ z
dtr1-aux↓' {X} {Y} {z} .(now z) .(now z) (now x) now∼ now↓ = now↓
dtr1-aux↓' {X} {Y} {z} dx .(now z) (later dy) () now↓
dtr1-aux↓' (later dx) (later dz) (now y) (later∼ p) (later↓ q) = 
  later↓ (dtr1-aux↓' (♭ dx) (♭ dz) (now y) (♭ p) q)
dtr1-aux↓' (now x) (later dz) (later dy) (later∼ p) (later↓ q) = 
  later↓ (dtr1-aux↓' (now x) (♭ dz) (♭ dy) (♭ p) q)
dtr1-aux↓' (later dx) (later dz) (later dy) (later∼ p) (later↓ q) with ♭ dz
... | a with
 trans∼ (sym∼ (dbindlater {f = λ _ → dx} (♭ dy))) (♭ p)
dtr1-aux↓' (later dx) (later dz) (later dy) (later∼ p) (later↓ (later↓ q)) | 
  .(later dw) | later∼ {._} {dw} r = 
  later↓ (dtr1-aux↓' (♭ dx) (♭ dw) (♭ dy) (♭ r) q)

dtr1-aux↓ : ∀{X Y}{z : X}(dx : Delay X)(dy : Delay Y) →
            dbind (λ _ → dx) dy ↓ z → dbind (hom dp₁) d⟨ dx , dy ⟩-aux ↓ z
dtr1-aux↓ dx dy p = dtr1-aux↓' dx _ dy refl∼ p

dtr1-aux≈ : ∀{X Y}(dx dz : Delay X)(dy : Delay Y) →
            dbind (λ _ → dx) dy ≈ dz → 
            dbind (hom dp₁) d⟨ dx , dy ⟩-aux ≈ dz
dtr1-aux≈ (now x) (now .x) (now y) (↓≈ now↓ now↓) = ↓≈ now↓ now↓
dtr1-aux≈ (now x) (later dy) (now y) (↓≈ now↓ (later↓ q)) = ↓≈ now↓ (later↓ q)
dtr1-aux≈ (now x) (now z) (later dy) (↓≈ (later↓ p) now↓) = 
  ↓≈ (later↓ (dtr1-aux↓ (now x) (♭ dy) p)) now↓
dtr1-aux≈ (now x) (later dz) (later dy) (↓≈ (later↓ p) (later↓ q)) = 
  later≈ (♯ (dtr1-aux≈ (now x) (♭ dz) (♭ dy) (↓≈ p q)))
dtr1-aux≈ (now x) (later dz) (later dy) (later≈ p) = 
  later≈ (♯ (dtr1-aux≈ (now x) (♭ dz) (♭ dy) (♭ p)))
dtr1-aux≈ (later dx) (now z) (now y) (↓≈ (later↓ p) now↓) = 
  ↓≈ (later↓ (dtr1-aux↓ (♭ dx) (now y) p)) now↓
dtr1-aux≈ (later dx) (later dz) (now y) (↓≈ (later↓ p) (later↓ q)) = 
  ↓≈ (later↓ (dtr1-aux↓ (♭ dx) (now y) p)) (later↓ q)
dtr1-aux≈ (later dx) (later dz) (now y) (later≈ p) = 
  later≈ (♯ dtr1-aux≈ (♭ dx) (♭ dz) (now y) (♭ p))
dtr1-aux≈ (later dx) dz (later dy) (↓≈ (later↓ p) q) with
  ≈↓ (∼→≈ (dbindlater {f = λ _ → dx} (♭ dy))) p
dtr1-aux≈ (later dx) (now z) (later dy) (↓≈ (later↓ p) now↓) | later↓ r = 
  ↓≈ (later↓ (dtr1-aux↓ (♭ dx) (♭ dy) r)) now↓
dtr1-aux≈ (later dx) (later dz) (later dy) (↓≈ (later↓ p) q) | later↓ r = 
  ↓≈ (later↓ (dtr1-aux↓ (♭ dx) (♭ dy) r)) q
dtr1-aux≈ (later dx) (later dz) (later dy) (later≈ p) with
  trans≈ laterlem 
         (trans≈ (later≈ (♯ refl≈)) 
                 (trans≈ (∼→≈ (sym∼ (dbindlater {f = λ _ → dx} (♭ dy)))) (♭ p)))
... | q = later≈ (♯ (dtr1-aux≈ (♭ dx) (♭ dz) (♭ dy) q))

dtr1-aux : ∀{X Y}(dx : Delay X)(dy : Delay Y) →
           dbind (hom dp₁) d⟨ dx , dy ⟩-aux ≈ dbind (λ _ → dx) dy
dtr1-aux dx dy = dtr1-aux≈ dx _ dy refl≈

dtr1 : ∀{X Y Z}{f : Z → Delay X}{g : Z → Delay Y}(z : Z) → 
       comp (hom dp₁) d⟨ f , g ⟩ z ≅ comp f (drest g) z
dtr1 {X}{Y}{Z}{f}{g} z = 
  proof
  comp (hom dp₁) d⟨ f , g ⟩ z
  ≅⟨ quotient (dtr1-aux (f z) (g z)) ⟩
  dbind (λ _ → f z) (g z)
  ≅⟨ compdrest {f = f} {g = g} z ⟩
  dbind f (dbind (λ a → now z) (g z))
  ≅⟨ cong (dbind f) (sym (drest≅ z g)) ⟩ 
  dbind f (drest g z)
  ∎

-- Second triangle commutes

dtr2-aux↓' : ∀{X Y}{z : Y}(dx : Delay X)(dz dy : Delay Y) →
             dbind (λ _ → dy) dx ∼ dz → dz ↓ z → 
             dbind (hom dp₂) d⟨ dx , dy ⟩-aux ↓ z
dtr2-aux↓' (now x) .(now y) (now y) now∼ q = q
dtr2-aux↓' (now x) (later dz) (later dy) (later∼ p) (later↓ q) = 
  later↓ (dtr2-aux↓' (now x) (♭ dz) (♭ dy) (♭ p) q)
dtr2-aux↓' (later dx) (later dz) (now y) (later∼ p) (later↓ q) = 
  later↓ (dtr2-aux↓' (♭ dx) (♭ dz) (now y) (♭ p) q)
dtr2-aux↓' (later dx) (later dz) (later dy) (later∼ p) (later↓ q) with ♭ dz
... | a with
 trans∼ (sym∼ (dbindlater {f = λ _ → dy} (♭ dx))) (♭ p)
dtr2-aux↓' (later dx) (later dz) (later dy) (later∼ p) (later↓ (later↓ q)) | 
  .(later dw) | later∼ {._} {dw} r = 
  later↓ (dtr2-aux↓' (♭ dx) (♭ dw) (♭ dy) (♭ r) q)

dtr2-aux↓ : ∀{X Y}{z : Y}(dx : Delay X)(dy : Delay Y) →
            dbind (λ _ → dy) dx ↓ z → dbind (hom dp₂) d⟨ dx , dy ⟩-aux ↓ z
dtr2-aux↓ dx dy p = dtr2-aux↓' dx _ dy refl∼ p

dtr2-aux≈ : ∀{X Y}(dx : Delay X)(dz dy : Delay Y) →
            dbind (λ _ → dy) dx ≈ dz → 
            dbind (hom dp₂) d⟨ dx , dy ⟩-aux ≈ dz
dtr2-aux≈ (now x) (now y) (now .y) (↓≈ now↓ now↓) = ↓≈ now↓ now↓
dtr2-aux≈ (now x) (later dz) (now y) (↓≈ now↓ (later↓ q)) = ↓≈ now↓ (later↓ q)
dtr2-aux≈ (now x) (now z) (later dy) (↓≈ (later↓ p) now↓) = 
  ↓≈ (later↓ (dtr2-aux↓ (now x) (♭ dy) p)) now↓
dtr2-aux≈ (now x) (later dz) (later dy) (↓≈ (later↓ p) (later↓ q)) = 
  ↓≈ (later↓ (dtr2-aux↓ (now x) (♭ dy) p)) (later↓ q)
dtr2-aux≈ (now x) (later dz) (later dy) (later≈ p) = 
  later≈ (♯ dtr2-aux≈ (now x) (♭ dz) (♭ dy) (♭ p))
dtr2-aux≈ (later dx) (now z) (now y) (↓≈ (later↓ p) now↓) = 
  ↓≈ (later↓ (dtr2-aux↓ (♭ dx) (now y) p)) now↓
dtr2-aux≈ (later dx) (later dz) (now y) (↓≈ (later↓ p) (later↓ q)) = 
  later≈ (♯ (dtr2-aux≈ (♭ dx) (♭ dz) (now y) (↓≈ p q)))
dtr2-aux≈ (later dx) (later dz) (now y) (later≈ p) = 
  later≈ (♯ (dtr2-aux≈ (♭ dx) (♭ dz) (now y) (♭ p)))
dtr2-aux≈ (later dx) (now x) (later dy) (↓≈ (later↓ p) now↓) with
  ≈↓ (∼→≈ (dbindlater {f = λ _ → dy} (♭ dx))) p
dtr2-aux≈ (later dx) (now x) (later dy) (↓≈ (later↓ p) now↓) | later↓ q = 
  ↓≈ (later↓ (dtr2-aux↓ (♭ dx) (♭ dy) q)) now↓
dtr2-aux≈ (later dx) (later dz) (later dy) (↓≈ (later↓ p) (later↓ q)) with
  ≈↓ (∼→≈ (dbindlater {f = λ _ → dy} (♭ dx))) p 
dtr2-aux≈ (later dx) (later dz) (later dy) (↓≈ (later↓ p) (later↓ q)) | later↓ r
 = ↓≈ (later↓ (dtr2-aux↓ (♭ dx) (♭ dy) r)) (later↓ q)
dtr2-aux≈ (later dx) (later dz) (later dy) (later≈ p) with
  trans≈ laterlem 
         (trans≈ (later≈ (♯ refl≈)) 
                 (trans≈ (∼→≈ (sym∼ (dbindlater {f = λ _ → dy} (♭ dx)))) (♭ p)))
... | q = later≈ (♯ (dtr2-aux≈ (♭ dx) (♭ dz) (♭ dy) q))

dtr2-aux : ∀{X Y}(dx : Delay X)(dy : Delay Y) →
           dbind (hom dp₂) d⟨ dx , dy ⟩-aux ≈ dbind (λ _ → dy) dx
dtr2-aux dx dy = dtr2-aux≈ dx _ dy refl≈

dtr2 : ∀{X Y Z}{f : Z → Delay X}{g : Z → Delay Y}(z : Z) → 
       comp (hom dp₂) d⟨ f , g ⟩ z ≅ comp g (drest f) z
dtr2 {X}{Y}{Z}{f}{g} z = 
  proof
  comp (hom dp₂) d⟨ f , g ⟩ z
  ≅⟨ quotient (dtr2-aux (f z) (g z)) ⟩
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

-- Meets

open import Order DelayR
open Meets
open import Relation.Binary
open import Relation.Nullary.Core

dMt1-aux  : ∀{X}{_≟_ : Decidable {A = X} _≅'_}(dx : Delay X) → 
            dmeet-aux {X}{_≟_} dx dx ≈ dx
dMt1-aux {X}{_≟_} (now x) with x ≟ x
dMt1-aux (now x) | yes refl = ↓≈ now↓ now↓
dMt1-aux (now x) | no ¬p with ¬p refl
dMt1-aux (now x) | no ¬p | ()
dMt1-aux (later dx) = later≈ (♯ (dMt1-aux (♭ dx)))

dMt1  : ∀{X Y}{_≟_ : Decidable {A = Y}{B = Y} _≅'_}{f : X → Delay Y} → 
        (x : X) → dmeet {X}{Y}{_≟_} f f x ≅ f x
dMt1 {f = f} x = quotient (dMt1-aux (f x))

dMt2a-aux↓' : ∀{X}{_≟_ : Decidable {A = X} _≅'_}{z : X}(dx dy dz : Delay X) →
              dbind (λ _ → dy) (dmeet-aux {X}{_≟_} dx dy) ∼ dz → dz ↓ z → 
              dmeet-aux {X}{_≟_} dx dy ↓ z
dMt2a-aux↓' {X}{_≟_} (now x) (now y) dz p q with x ≟ y 
dMt2a-aux↓' (now x) (now .x) .(now x) now∼ q | yes refl = q
dMt2a-aux↓' (now x) (now y) (later dz) (later∼ p) (later↓ q) | no ¬r = 
  later↓ (dMt2a-aux↓' (now x) (now y) (♭ dz) (♭ p) q)
dMt2a-aux↓' {X}{_≟_} (now x) (later dy) (later .dz) (later∼ p) (later↓ {dz} q) with ♭ dz
... | dw with
  trans∼ (sym∼ (dbindlater {_}{_}{λ _ → dy} (dmeet-aux {X}{_≟_} (now x) (♭ dy)))) (♭ p)
dMt2a-aux↓' (now x) (later dy) (later .dz) (later∼ p) (later↓ {dz} (later↓ {dw} q)) | .(later dw) | later∼ r = 
  later↓ (dMt2a-aux↓' (now x) (♭ dy) (♭ dw) (♭ r) q)
dMt2a-aux↓' (later dx) (now y) (later .dz) (later∼ p) (later↓ {dz} q) = 
  later↓ (dMt2a-aux↓' (♭ dx) (now y) (♭ dz) (♭ p) q)
dMt2a-aux↓' {X}{_≟_} (later dx) (later dy) (later .dz) (later∼ p) (later↓ {dz} q) with ♭ dz
... | dw with
  trans∼ (sym∼ (dbindlater {_}{_}{λ _ → dy} (dmeet-aux {X}{_≟_} (♭ dx) (♭ dy)))) (♭ p)
dMt2a-aux↓' (later dx) (later dy) (later .dz) (later∼ p) (later↓ {dz} (later↓ {dw} q)) | .(later dw) | later∼ r = later↓ (dMt2a-aux↓' (♭ dx) (♭ dy) (♭ dw) (♭ r) q)

dMt2a-aux↓ : ∀{X}{_≟_ : Decidable {A = X} _≅'_}{z : X}(dx dy : Delay X) →
             dbind (λ _ → dy) (dmeet-aux {X}{_≟_} dx dy) ↓ z →  
             dmeet-aux {X}{_≟_} dx dy ↓ z
dMt2a-aux↓ dx dy p = dMt2a-aux↓' dx dy _ refl∼ p

dMt2a-aux' : ∀{X}{_≟_ : Decidable {A = X} _≅'_}(dx dy dz : Delay X) →
            dbind (λ _ → dy) (dmeet-aux {X}{_≟_} dx dy) ≈ dz →  
            dmeet-aux {X}{_≟_} dx dy ≈ dz
dMt2a-aux' {X}{_≟_} (now x) (now y) dz p with x ≟ y 
dMt2a-aux' (now x) (now .x) dz p | yes refl = p
dMt2a-aux' (now x) (now y) (now z) (↓≈ (later↓ p) now↓) | no ¬q = 
  ↓≈ (later↓ (dMt2a-aux↓ (now x) (now y) p)) now↓
dMt2a-aux' (now x) (now y) (later dz) (↓≈ (later↓ p) (later↓ r)) | no ¬q = 
  later≈ (♯ (dMt2a-aux' (now x) (now y) (♭ dz) (↓≈ p r)))
dMt2a-aux' (now x) (now y) (later dz) (later≈ p) | no ¬q = 
  later≈ (♯ (dMt2a-aux' (now x) (now y) (♭ dz) (♭ p)))
dMt2a-aux' {X}{_≟_} (now x) (later dy) (now z) (↓≈ (later↓ p) now↓) with
  trans≈ (∼→≈ (dbindlater {_}{_}{λ _ → dy} (dmeet-aux {X}{_≟_} (now x) (♭ dy)))) (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem))
dMt2a-aux' (now x) (later dy) (now z) (↓≈ (later↓ p) now↓) | r = 
  ↓≈ (later↓ (dMt2a-aux↓ (now x) (♭ dy) (≈↓ r p))) now↓
dMt2a-aux' {X}{_≟_} (now x) (later dy) (later dz) (↓≈ (later↓ p) (later↓ q)) with
  trans≈ (∼→≈ (dbindlater {_}{_}{λ _ → dy} (dmeet-aux {X}{_≟_} (now x) (♭ dy)))) (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem))
dMt2a-aux' (now x) (later dy) (later dz) (↓≈ (later↓ p) (later↓ q)) | r =
  later≈ (♯ (dMt2a-aux' (now x) (♭ dy) (♭ dz) (↓≈ (≈↓ r p) q)))
dMt2a-aux' {X}{_≟_} (now x) (later dy) (later dz) (later≈ p) with
  trans≈ (∼→≈ (dbindlater {_}{_}{λ _ → dy} (dmeet-aux {X}{_≟_} (now x) (♭ dy)))) (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem))
dMt2a-aux' (now x) (later dy) (later dz) (later≈ p) | r = 
  later≈ (♯ (dMt2a-aux' (now x) (♭ dy) (♭ dz) (trans≈ (sym≈ r) (♭ p))))
dMt2a-aux' (later dx) (now y) (now z) (↓≈ (later↓ p) now↓) = 
  ↓≈ (later↓ (dMt2a-aux↓ (♭ dx) (now y) p)) now↓
dMt2a-aux' (later dx) (now y) (later dz) (↓≈ (later↓ p) (later↓ q)) = 
  later≈ (♯ (dMt2a-aux' (♭ dx) (now y) (♭ dz) (↓≈ p q)))
dMt2a-aux' (later dx) (now y) (later dz) (later≈ p) = 
  later≈ (♯ (dMt2a-aux' (♭ dx) (now y) (♭ dz) (♭ p)))
dMt2a-aux' {X}{_≟_} (later dx) (later dy) (now z) (↓≈ (later↓ p) now↓) with 
  trans≈ (∼→≈ (dbindlater {_}{_}{λ _ → dy} (dmeet-aux {X}{_≟_} (♭ dx) (♭ dy)))) (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem))
... | r = ↓≈ (later↓ (dMt2a-aux↓ (♭ dx) (♭ dy) (≈↓ r p))) now↓
dMt2a-aux' {X}{_≟_} (later dx) (later dy) (later dz) (↓≈ (later↓ p) (later↓ q)) with
  trans≈ (∼→≈ (dbindlater {_}{_}{λ _ → dy} (dmeet-aux {X}{_≟_} (♭ dx) (♭ dy)))) (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem))
... | r = later≈ (♯ (dMt2a-aux' (♭ dx) (♭ dy) (♭ dz) (↓≈ (≈↓ r p) q)))
dMt2a-aux' {X}{_≟_} (later dx) (later dy) (later dz) (later≈ p) with
  trans≈ (∼→≈ (dbindlater {_}{_}{λ _ → dy} (dmeet-aux {X}{_≟_} (♭ dx) (♭ dy)))) (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem))
... | r = later≈ (♯ (dMt2a-aux' (♭ dx) (♭ dy) (♭ dz) (trans≈ (sym≈ r) (♭ p))))

dMt2a-aux : ∀{X}{_≟_ : Decidable {A = X} _≅'_}(dx dy : Delay X) →
            dmeet-aux {X}{_≟_} dx dy ≈ 
            dbind (λ _ → dy) (dmeet-aux {X}{_≟_} dx dy)
dMt2a-aux dx dy = dMt2a-aux' dx dy _ refl≈

dMt2a : ∀{X Y}{_≟_ : Decidable {A = Y}{B = Y} _≅'_}{f g : X → Delay Y} →
        dmeet {X}{Y}{_≟_} f g ≤ g
dMt2a {X}{Y}{_≟_}{f}{g} = ext (λ x → 
  proof 
  dbind g (drest (dmeet f g) x)
  ≅⟨ cong (dbind g) (drest≅ x (dmeet f g)) ⟩
  dbind g (dbind (λ z → now x) (dmeet f g x))
  ≅⟨ sym (compdrest {f = g}{g = dmeet f g} x) ⟩
  dbind (λ _ → g x) (dmeet f g x)
  ≅⟨ quotient (sym≈ (dMt2a-aux (f x) (g x))) ⟩
  dmeet f g x
  ∎)

-- dMt2b is the same
-}

-- Joins

open import Order DelayR

dbindcomm : {X Y : Set}{f g : X → Delay Y} → f ⌣ g → (x : X) →
        dbind (λ _ → g x) (f x) ≅ dbind (λ _ → f x) (g x)
dbindcomm {f = f} {g = g} p x = 
  proof
  dbind (λ _ → g x) (f x) 
  ≅⟨ compdrest {f = g} {g = f} x ⟩
  dbind g (dbind (λ _ → now x) (f x))
  ≅⟨ cong (dbind g) (sym (drest≅ x f)) ⟩
  dbind g (drest f x)
  ≅⟨ cong (λ h → h x) p ⟩
  dbind f (drest g x)
  ≅⟨ cong (dbind f) (drest≅ x g) ⟩
  dbind f (dbind (λ _ → now x) (g x))
  ≅⟨ sym (compdrest {f = f} {g = g} x) ⟩
  dbind (λ _ → f x) (g x)
  ∎

_d⌣_ : ∀{X Y}(f g : X → Delay Y) → Set
_d⌣_ {X} f g = {x : X} → dbind (λ _ → g x) (f x) ≈ dbind (λ _ → f x) (g x)

djoin-aux : ∀{X}(dx dy : Delay X) → dbind (λ _ → dy) dx ≈ dbind (λ _ → dx) dy →
            Delay X
djoin-aux (now x) (now .x) (↓≈ now↓ now↓) = now x
djoin-aux (now x) (later dy) p = now x
djoin-aux (later dx) (now y) p = now y
djoin-aux (later dx) (later dy) (↓≈ (later↓ {._}{x} p) (later↓ q)) = now x
djoin-aux (later dx) (later dy) (later≈ p) with  
  trans≈ (dbindlater≈ (♭ dx)) (trans≈ (♭ p) (sym≈ (dbindlater≈ (♭ dy))))
... | r = later (♯ (djoin-aux (♭ dx) (♭ dy) r))

djoin : {X Y : Set}(f g : X → Delay Y) → f d⌣ g → X → Delay Y
djoin f g p x = djoin-aux (f x) (g x) p

dbindconst↓ : ∀{X Y}{x : X}{y : Y}(dx : Delay X){dy : Delay Y} → dx ↓ x → 
              dy ↓ y → dbind (λ _ → dy) dx ↓ y
dbindconst↓ (now x) p q = q
dbindconst↓ (later dx) (later↓ p) q = later↓ (dbindconst↓ (♭ dx) p q) 

dbindconst↓-arg₁' : ∀{X}{x : X}(dx dy dz dz' : Delay X) → 
                    dbind (λ _ → dy) dx ∼ dz → dbind (λ _ → dx) dy ∼ dz' → 
                    dz ↓ x → dz' ↓ x → dx ↓ x
dbindconst↓-arg₁' (now x) (now y) dz dz' p q r r' with
  unique↓ r' (∼↓ q now↓)
dbindconst↓-arg₁' {X} {x} (now .x) (now y) dz dz' p q r r' | refl = now↓
dbindconst↓-arg₁' (now x) (later .dy) .(later dz) .(later dz') (later∼ {dy} {dz} p) (later∼ {._} {dz'} q) (later↓ r) (later↓ r') = dbindconst↓-arg₁' (now x) (♭ dy) (♭ dz) (♭ dz') (♭ p) (♭ q) r r'
dbindconst↓-arg₁' (later dx) (now y) dz .(later dz') p (later∼ {.dx} {dz'} q) r (later↓ r') = later↓ (∼↓ (sym∼ (♭ q)) r') 
dbindconst↓-arg₁' (later dx) (later dy) (now z) dz' () q r r'
dbindconst↓-arg₁' (later dx) (later dy) (later dz) (now z') p () r r'
dbindconst↓-arg₁' (later dx) (later dy) (later dz) (later dz') (later∼ p) (later∼ q) (later↓ r) (later↓ r') with ♭ dz |
                                    ♭ dz' |
                                    trans∼ (sym∼ (dbindlater (♭ dx))) (♭ p) |
                                    trans∼ (sym∼ (dbindlater (♭ dy))) (♭ q)
dbindconst↓-arg₁' (later dx) (later dy) (later dz) (later dz') (later∼ p) (later∼ q) (later↓ (later↓ r)) (later↓ (later↓ r'))| later dw | later dw' | later∼ s | later∼ t = 
  later↓ (dbindconst↓-arg₁' (♭ dx) (♭ dy) (♭ dw) (♭ dw') (♭ s) (♭ t) r r')

dbindconst↓-arg₁ : ∀{X}{x : X}(dx dy : Delay X) → dbind (λ _ → dy) dx ↓ x →
                   dbind (λ _ → dx) dy ↓ x → dx ↓ x
dbindconst↓-arg₁ dx dy p q = dbindconst↓-arg₁' dx dy _ _ refl∼ refl∼ p q

djoin-aux↓ : ∀{X}{x : X}(dx dy : Delay X) → 
             (p : dbind (λ _ → dy) dx ≈ dbind (λ _ → dx) dy) → dx ↓ x →  
             djoin-aux dx dy p ↓ x
djoin-aux↓ (now x) (now .x) (↓≈ now↓ now↓) now↓ = now↓
djoin-aux↓ (now x) (later dy) p now↓ = now↓
djoin-aux↓ (later dx) (now y) (↓≈ (later↓ p) (later↓ p')) (later↓ q) with
  unique↓ p' q | unique↓ p (dbindconst↓ (♭ dx) q now↓)
djoin-aux↓ {X} {x} (later dx) (now .x) (↓≈ (later↓ p) (later↓ p')) (later↓ q) | refl | refl = now↓
djoin-aux↓ (later dx) (now y) (later≈ p) (later↓ q) with
  unique↓ (≈↓ (sym≈ (♭ p)) q) (dbindconst↓ (♭ dx) q now↓)
djoin-aux↓ {X} {x} (later dx) (now .x) (later≈ p) (later↓ q) | refl = now↓
djoin-aux↓ (later dx) (later dy) (↓≈ (later↓ {y = y} p) (later↓ p')) (later↓ q) with
  ∼↓ (dbindlater (♭ dx)) p |
  ∼↓ (dbindlater (♭ dy)) p'
djoin-aux↓ (later dx) (later dy) (↓≈ (later↓ p) (later↓ p')) (later↓ q) | later↓ r | later↓ s with
  unique↓ q (dbindconst↓-arg₁ (♭ dx) (♭ dy) r s)
djoin-aux↓ (later dx) (later dy) (↓≈ (later↓ p) (later↓ p')) (later↓ q) | later↓ r | later↓ s | refl = now↓ 
djoin-aux↓ (later dx) (later dy) (later≈ p) (later↓ q) with
  trans≈ (dbindlater≈ (♭ dx)) (trans≈ (♭ p) (sym≈ (dbindlater≈ (♭ dy))))
... | r = later↓ (djoin-aux↓ (♭ dx) (♭ dy) r q)               

djoin-aux-eq : ∀{X}(dx dy : Delay X) → 
                {p q : dbind (λ _ → dy) dx ≈ dbind (λ _ → dx) dy} → 
                djoin-aux dx dy p ≈ djoin-aux dx dy q
djoin-aux-eq (now x) (now .x) {↓≈ now↓ now↓} {↓≈ now↓ now↓} = ↓≈ now↓ now↓
djoin-aux-eq (now x) (later dy) = refl≈
djoin-aux-eq (later dx) (now y) = refl≈
djoin-aux-eq (later dx) (later dy) {↓≈ (later↓ p) (later↓ p')} {↓≈ (later↓ q) (later↓ q')} with unique↓ p q 
djoin-aux-eq (later dx) (later dy) {↓≈ (later↓ p) (later↓ p')} {↓≈ (later↓ q) (later↓ q')} | refl = refl≈
djoin-aux-eq (later dx) (later dy) {↓≈ (later↓ p) (later↓ p')} {later≈ q} with  
  trans≈ (dbindlater≈ (♭ dx)) (trans≈ (♭ q) (sym≈ (dbindlater≈ (♭ dy)))) |
  ∼↓ (dbindlater (♭ dx)) p |
  ∼↓ (dbindlater (♭ dy)) p'
... | r | later↓ s | later↓ t = ↓≈ now↓ (later↓ (djoin-aux↓ (♭ dx) (♭ dy) r (dbindconst↓-arg₁ (♭ dx) (♭ dy) s t)))
djoin-aux-eq (later dx) (later dy) {later≈ p} {↓≈ (later↓ q) (later↓ q')} with  
  trans≈ (dbindlater≈ (♭ dx)) (trans≈ (♭ p) (sym≈ (dbindlater≈ (♭ dy)))) |
  ∼↓ (dbindlater (♭ dx)) q |
  ∼↓ (dbindlater (♭ dy)) q'
... | r | later↓ s | later↓ t = ↓≈ (later↓ (djoin-aux↓ (♭ dx) (♭ dy) r (dbindconst↓-arg₁ (♭ dx) (♭ dy) s t))) now↓
djoin-aux-eq (later dx) (later dy) {later≈ p} {later≈ q} with  
  trans≈ (dbindlater≈ (♭ dx)) (trans≈ (♭ p) (sym≈ (dbindlater≈ (♭ dy)))) |
  trans≈ (dbindlater≈ (♭ dx)) (trans≈ (♭ q) (sym≈ (dbindlater≈ (♭ dy))))
... | r | r' = later≈ (♯ (djoin-aux-eq (♭ dx) (♭ dy) {r} {r'}))

dbindconst≈ : ∀{X}{dx dy dz : Delay X} → dy ≅ dz → 
              dbind (λ _ → dy) dx ≈ dbind (λ _ → dz) dx
dbindconst≈ refl = refl≈

dJn1a-aux'' : ∀{X}(dx dy dz : Delay X)
              (p : dbind (λ _ → dy) dx ≈ dbind (λ _ → dx) dy) →
              dbind (λ _ → djoin-aux dx dy p) dx ≈ dz → dx ≈ dz
dJn1a-aux'' (now x) (now .x) dz (↓≈ now↓ now↓) q = q
dJn1a-aux'' (now x) (later dy) dz p q = q
dJn1a-aux'' (later .dy) (now y) (now z) (↓≈ (later↓ p) (later↓ {dy} q)) (↓≈ (later↓ r) now↓) with unique↓ p r
dJn1a-aux'' (later .dy) (now y) (now z) (↓≈ (later↓ p) (later↓ {dy} q)) (↓≈ (later↓ r) now↓) | refl = ↓≈ (later↓ q) now↓
dJn1a-aux'' (later .dy) (now y) (later dz) (↓≈ (later↓ p) (later↓ {dy} q)) (↓≈ (later↓ r) (later↓ s)) with unique↓ p r
dJn1a-aux'' (later .dy) (now y) (later dz) (↓≈ (later↓ p) (later↓ {dy} q)) (↓≈ (later↓ r) (later↓ s)) | refl = ↓≈ (later↓ q) (later↓ s)
dJn1a-aux'' (later .dy) (now y) (later dz) (↓≈ (later↓ p) (later↓ {dy} q)) (later≈ r) = ↓≈ (later↓ q) (later↓ (≈↓ (♭ r) p))
dJn1a-aux'' (later dx) (now y) (now z) (later≈ p) (↓≈ (later↓ q) now↓) = 
  ↓≈ (later↓ (≈↓ (♭ p) q)) now↓
dJn1a-aux'' (later dx) (now y) (later dz) (later≈ p) (↓≈ (later↓ q) (later↓ r)) = later≈ (♯ (↓≈ (≈↓ (♭ p) q) r))
dJn1a-aux'' (later dx) (now y) (later dz) (later≈ p) (later≈ q) = 
  later≈ (♯ (trans≈ (sym≈ (♭ p)) (♭ q)))
dJn1a-aux'' (later dx) (later dy) (now z) (↓≈ (later↓ {y = y} p) (later↓ q)) (↓≈ (later↓ r) now↓) with 
  ∼↓ (dbindlater (♭ dx)) p |
  ∼↓ (dbindlater (♭ dy)) q
... | later↓ s | later↓ t with
  dbindconst↓-arg₁ (♭ dx) (♭ dy) s t
... | u  with 
  unique↓ r (dbindconst↓ (♭ dx) {now y} u now↓) 
dJn1a-aux'' (later dx) (later dy) (now .y) (↓≈ (later↓ {._} {y} p) (later↓ q)) (↓≈ (later↓ r) now↓) | later↓ s | later↓ t | u | refl = ↓≈ (later↓ u) now↓
dJn1a-aux'' (later dx) (later dy) (later dz) (↓≈ (later↓ {y = y} p) (later↓ q)) (↓≈ (later↓ {y = y'} r) (later↓ s)) with
  ∼↓ (dbindlater (♭ dx)) p |
  ∼↓ (dbindlater (♭ dy)) q
... | later↓ t | later↓ u with
  dbindconst↓-arg₁ (♭ dx) (♭ dy) t u
... | v with 
  unique↓ r (dbindconst↓ (♭ dx) {now y} v now↓)
dJn1a-aux'' (later dx) (later dy) (later dz) (↓≈ (later↓ p) (later↓ q)) (↓≈ (later↓ r) (later↓ s)) | later↓ t | later↓ u | v | refl = ↓≈ (later↓ v) (later↓ s)
dJn1a-aux'' (later dx) (later dy) (later dz) (↓≈ (later↓ {y = y} p) (later↓ q)) (later≈ r) with
  ∼↓ (dbindlater (♭ dx)) p |
  ∼↓ (dbindlater (♭ dy)) q
... | later↓ s | later↓ t with
  dbindconst↓-arg₁ (♭ dx) (♭ dy) s t
... | u = later≈ (♯ (trans≈ (↓≈ u (dbindconst↓ (♭ dx) {now y} u now↓)) (♭ r)))
dJn1a-aux'' (later dx) (later dy) (now z) (later≈ p) (↓≈ (later↓ q) now↓) = 
  ↓≈ (later↓ {!!}) now↓
dJn1a-aux'' (later dx) (later dy) (later dz) (later≈ p) (↓≈ (later↓ q) (later↓ r)) = {!!}
{-
with
  trans≈ laterlem
         (trans≈ (later≈ (♯ refl≈)) 
                 (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → dy} (♭ dx))))) | 
  trans≈ laterlem
         (trans≈ (later≈ (♯ refl≈)) 
                 (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → dx} (♭ dy)))))
... | s | t with
  trans≈ laterlem
         (trans≈ (later≈ (♯ refl≈)) 
                 (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → ♯ (djoin-aux (♭ dx) (♭ dy) (trans≈ s (trans≈ (♭ p) (sym≈ t))))} (♭ dx)))))
... | u = later≈ (♯ dJn1a-aux'' (♭ dx) (♭ dy) (♭ dz) (trans≈ s (trans≈ (♭ p) (sym≈ t))) (trans≈ u (trans≈ (dbindconst≈ {dy = later (♯ (djoin-aux (♭ dx) (♭ dy) (trans≈ s (trans≈ (♭ p) (sym≈ t)))))} (quotient (later≈ (♯ {!!})))) (↓≈ q r))))
-}

--{dy = later (♯ (djoin-aux (♭ dx) (♭ dy) (trans≈ s (trans≈ (♭ p) (sym≈ t)))))}

--(λ x → _ ≈ dbind (λ _ → x) (♭ dx)) (quotient (later≈ (♯ refl≈))) {!!}) (↓≈ q r))))

dJn1a-aux'' (later dx) (later dy) (later dz) (later≈ p) (later≈ q) with 
  trans≈ (dbindlater≈ (♭ dx)) (trans≈ (♭ p) (sym≈ (dbindlater≈ (♭ dy))))
... | r = 
  later≈ (♯ 
    (dJn1a-aux'' (♭ dx) (♭ dy) (♭ dz) r        
       (trans≈ (dbindlater≈ (♭ dx)) 
               (trans≈ (dbindconst≈ {_}
                                    {♭ dx}
                                    {later (♯ (djoin-aux (♭ dx) (♭ dy) r))}
                                    (quotient (later≈ (♯ djoin-aux-eq (♭ dx)
                                                                      (♭ dy))))) 
                       (♭ q)))))

{-
dJn1a-aux'' (later dx) (later dy) (later dz) (later≈ p) (later≈ q) = 
  later≈ 
    (♯ 
      (dJn1a-aux'' (♭ dx) 
                   (♭ dy) 
                   (♭ dz) 
                   (trans≈ laterlem 
                     (trans≈ (later≈ (♯ refl≈)) 
                       (trans≈ (∼→≈ (sym∼ (dbindlater {_} 
                                                      {_} 
                                                      {λ _ → dy} 
                                                      (♭ dx)))) 
                         (trans≈ (♭ p) 
                           (trans≈ (∼→≈ (dbindlater {_} {_} {λ _ → dx} (♭ dy))) 
                             (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem))))))) 
                   (trans≈ laterlem
                       (trans≈ (later≈ (♯ dbindconst≈ {_} {_}
                                            {djoin-aux (♭ dx) (♭ dy)
                                             (trans≈ laterlem
                                              (trans≈ (later≈ (♯ refl≈))
                                               (trans≈ (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → dy} (♭ dx))))
                                                (trans≈ (♭ p)
                                                 (trans≈ (∼→≈ (dbindlater {_} {_} {λ _ → dx} (♭ dy)))
                                                  (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem)))))))}
                                            {{!!}} {!!}))
                        (trans≈
                         (∼→≈
                          (sym∼ (dbindlater {_} {_} {λ _ → ♯ djoin-aux (♭ dx) (♭ dy) (trans≈ laterlem                                   
        (trans≈ (later≈ (♯ refl≈))                                             
          (trans≈ (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → dy} (♭ dx))))
            (trans≈ (♭ p)
              (trans≈ (∼→≈ (dbindlater {_} {_} {λ _ → dx} (♭ dy)))
                (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem)))))))} (♭ dx)))) (trans≈ {!!} (♭ q)))))))
-}





















{-♯ (djoin-aux (♭ dx) (♭ dy) 
(trans≈ laterlem                                   
        (trans≈ (later≈ (♯ refl≈))                                             
          (trans≈ (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → dy} (♭ dx))))
            (trans≈ (♭ p)
              (trans≈ (∼→≈ (dbindlater {_} {_} {λ _ → dx} (♭ dy)))
                (trans≈ (later≈ (♯ refl≈)) (sym≈ laterlem))))))))} {!♭ dx!})))
                        (♭ q)))))))
-}
{-
dbind
      (λ _ →
         djoin-aux (♭ dx) (♭ dy)
         (trans≈ laterlem
          (trans≈ (later≈ (.RestrictionDelay.♯-58 dx dy dz p q))
           (trans≈ (∼→≈ (sym∼ (dbindlater (♭ dx))))
            (trans≈ (♭ p)
             (trans≈ (∼→≈ (dbindlater (♭ dy)))
              (trans≈ (later≈ (.RestrictionDelay.♯-60 dx dy dz p q))
               (sym≈ laterlem))))))))
      (♭ dx)
      ≈ ♭ dz
-}  



{-
dJn1a-aux'' : ∀{X}(dx dy dz : Delay X)
              (p : dbind (λ _ → dy) dx ≈ dbind (λ _ → dx) dy) →
              dbind (λ _ → djoin-aux dx dy p) dx ∼ dz → dx ∼ dz
dJn1a-aux'' (now x) (now .x) dz (↓≈ now↓ now↓) q = q
dJn1a-aux'' (now x) (later dy) dz p q = q
dJn1a-aux'' (later dx) (now y) dz p q = {!!}
dJn1a-aux'' (later dx) (later dy) (now x) p ()
dJn1a-aux'' (later dx) (later dy) (later dz) (↓≈ (later↓ p) (later↓ q)) (later∼ r) = later∼ (♯ {!!})
dJn1a-aux'' (later dx) (later dy) (later dz) (later≈ p) (later∼ q) with
  trans≈ laterlem
         (trans≈ (later≈ (♯ refl≈)) 
                 (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → dy} (♭ dx))))) | 
  trans≈ laterlem
         (trans≈ (later≈ (♯ refl≈)) 
                 (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → dx} (♭ dy)))))
... | r | s with
  trans≈ laterlem
         (trans≈ (later≈ (♯ refl≈)) 
                 (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → ♯ (djoin-aux (♭ dx) (♭ dy) (trans≈ r (trans≈ (♭ p) (sym≈ s))))} (♭ dx)))))
... | t = later∼ (♯ (dJn1a-aux'' (♭ dx) (♭ dy) (♭ dz) (trans≈ r (trans≈ (♭ p) (sym≈ s))) {!trans≈ t (trans≈ ? (∼→≈ (♭ q)))!}))
-}

{-
dJn1a-aux' : ∀{X}(dx dy : Delay X)
             (p : dbind (λ _ → dy) dx ≈ dbind (λ _ → dx) dy) →
             dbind (λ _ → djoin-aux dx dy p) dx ∼ dx
dJn1a-aux' (now x) (now .x) (↓≈ now↓ now↓) = now∼
dJn1a-aux' (now x) (later x₁) p = now∼
dJn1a-aux' (later dx) (now y) p = dbind≈→∼ (later dx) p
dJn1a-aux' (later dx) (later dy) (↓≈ (later↓ p) (later↓ q)) = 
  later∼ (♯ (dbind≈→∼ (♭ dx) {!!}))
dJn1a-aux' (later dx) (later dy) (later≈ p) with
  trans≈ laterlem
         (trans≈ (later≈ (♯ refl≈)) 
                 (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → dy} (♭ dx))))) | 
  trans≈ laterlem
         (trans≈ (later≈ (♯ refl≈)) 
                 (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → dx} (♭ dy)))))
... | q | r with
  trans≈ laterlem
         (trans≈ (later≈ (♯ refl≈)) 
                 (∼→≈ (sym∼ (dbindlater {_} {_} {λ _ → ♯ (djoin-aux (♭ dx) (♭ dy) (trans≈ q (trans≈ (♭ p) (sym≈ r))))} (♭ dx)))))
... | s = later∼ (♯ {!!})

dJn1a : ∀{X Y}{f g : X → Delay Y}{p : f d⌣ g} → f ≤ djoin f g p
dJn1a {f = f}{g = g}{p = p} = ext (λ x → 
  proof
  dbind (djoin f g p) (drest f x)
  ≅⟨ cong (dbind (djoin f g p)) (drest≅ x f) ⟩
  dbind (djoin f g p) (dbind (λ _ → now x) (f x))
  ≅⟨ sym (compdrest {f = djoin f g p} {g = f} x) ⟩
  dbind (λ _ → djoin f g p x) (f x)
  ≅⟨ {!!} ⟩
  f x
  ∎)

{-
djoin : {X Y : Set}(f g : X → Delay Y)(x : X) →  
        dbind (λ _ → g x) (f x) ≈ dbind (λ _ → f x) (g x) → Delay Y
djoin f g x p = djoin-aux (f x) (g x) p

djoin' : {X Y : Set}(f g : X → Delay Y)(x : X) → f ⌣ g → Delay Y
djoin' f g x p = 
  djoin-aux (f x) 
            (g x) 
            (subst (_≈_ _)
                   (dbindcomm {f = f}{g = g} p x) 
                   refl≈)
-}
-}
-}