
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

dR1 : ∀{X Y}{f : X → Delay Y}(x : X) → (dbind f ∘ (drest f)) x ≅ f x
dR1 {f = f} x = 
  let open Monad DelayM 
  in proof
     dbind f (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x)))
     ≅⟨ cong (λ f' → dbind f (f' (f x))) (sym law3) ⟩
     dbind f (dbind (λ _ → now x) (f x))
     ≅⟨ cong (λ f' → f' (f x)) (sym law3) ⟩
     dbind (λ _ → f x) (f x)
     ≅⟨ quotient (sym≈ (lemma {_}{f x})) ⟩
     f x 
     ∎

dR2 : ∀{X Y Z}{f : X → Delay Y}{g : X → Delay Z}(x : X) → 
      (dbind (drest f) ∘ (drest g)) x ≅ (dbind (drest g) ∘ (drest f)) x
dR2 {f = f}{g = g} x =
  let open Monad DelayM 
  in proof 
     dbind
     (drest f)
     (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (g x)))
     ≅⟨ cong (λ f' → dbind (drest f) (f' (g x))) (sym law3) ⟩ 
     dbind (drest f) (dbind (λ _ → now x) (g x))
     ≅⟨ cong (λ f' → f' (g x)) (sym law3) ⟩ 
     dbind 
       (λ _ → dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x)))
       (g x)
     ≅⟨ cong (λ z → dbind (λ _ → z) (g x)) (cong (λ f' → f' (f x)) (sym law3)) ⟩
     dbind (λ _ → (dbind (λ _ → now x) (f x))) (g x)
     ≅⟨ quotient (∼→≈ (lemma2 {dy = f x}{dz = g x})) ⟩ 
     dbind (λ _ → (dbind (λ _ → now x) (g x))) (f x)
     ≅⟨ cong (λ z → dbind (λ _ → z) (f x)) (cong (λ f' → f' (g x)) law3) ⟩
     dbind 
       (λ _ → dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (g x)))
       (f x)
     ≅⟨ cong (λ f' → f' (f x)) law3 ⟩ 
     dbind (drest g) (dbind (λ _ → now x) (f x))
     ≅⟨ cong (λ f' → dbind (drest g) (f' (f x))) law3 ⟩ 
     dbind
     (λ y →
        dbind (now ∘ proj₁)
        (dbind (λ z → now (y , z)) (g y)))
     (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x)))
     ∎

dR3 : ∀{X Y Z}{f : X → Delay Y}{g : X → Delay Z}(x : X) → 
      (dbind (drest g) ∘ (drest f)) x ≅ drest (dbind g ∘ (drest f)) x
dR3 {f = f}{g = g} x = 
  let open Monad DelayM 
  in proof
     dbind
     (λ y →
        dbind (now ∘ proj₁)
        (dbind (λ z → now (y , z)) (g y)))
     (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x)))
     ≅⟨ cong (λ f' → dbind (drest g) (f' (f x))) (sym law3) ⟩ 
     dbind (drest g) (dbind (λ _ → now x) (f x))
     ≅⟨ cong (λ f' → f' (f x)) (sym law3) ⟩ 
     dbind 
       (λ _ → dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (g x)))
       (f x)
     ≅⟨ cong (λ z → dbind (λ _ → z) (f x)) (cong (λ f' → f' (g x)) (sym law3)) ⟩
     dbind (λ _ → (dbind (λ _ → now x) (g x))) (f x)
     ≅⟨ cong (λ h → h (f x)) law3 ⟩
     dbind (λ _ → now x) (dbind (λ _ → g x) (f x))
     ≅⟨ cong (λ h → dbind (λ _ → now x) (h (f x))) law3 ⟩
     dbind (λ _ → now x) (dbind g (dbind (λ _ → now x) (f x)))
     ≅⟨ cong (λ f' → f' (dbind g (dbind (λ _ → now x) (f x)))) law3 ⟩
     dbind (now ∘ proj₁)
       (dbind (λ y → now (x , y))
         (dbind g (dbind (λ _ → now x) (f x))))
     ≅⟨ cong 
          (λ f' → 
            dbind (now ∘ proj₁) 
              (dbind (λ y → now (x , y)) (dbind g (f' (f x))))) 
          law3 ⟩
     dbind (now ∘ proj₁)
      (dbind (λ y → now (x , y))
       (dbind g
        (dbind (now ∘ proj₁)
         (dbind (λ y → now (x , y)) (f x)))))
     ∎

dR4 : ∀{X Y Z}{f : X → Delay Y}{g : Y → Delay Z}(x : X) →
      (dbind (drest g) ∘ f) x ≅ (dbind f ∘ (drest (dbind g ∘ f))) x
dR4 {X}{Y}{Z}{f = f}{g = g} x = 
  let open Monad DelayM 
  in proof
    dbind
    (λ y →
       dbind (now ∘ proj₁) (dbind (λ z → now (y , z)) (g y)))
    (f x)
    ≅⟨ cong (λ t → dbind t (f x)) 
            (ext (λ y → cong (λ h → h (g y)) (sym law3))) ⟩
    dbind (λ y → dbind (λ _ → now y) (g y)) (f x)
    ≅⟨ quotient (lemma3 {dy = f x}{g = g}) ⟩
    dbind (λ y → dbind (λ _ → f x) (g y)) (f x)
    ≅⟨ cong (λ h → h (f x)) law3 ⟩
    dbind (λ _ → f x) (dbind g (f x))
    ≅⟨ cong (λ h → h (dbind g (f x))) law3 ⟩
    dbind f (dbind (λ _ → now x) (dbind g (f x)))
    ≅⟨ cong (λ h → dbind f (h (dbind g (f x)))) law3 ⟩
    dbind f
    (dbind (now ∘ proj₁)
     (dbind (λ y → now (x , y)) (dbind g (f x))))
    ∎

DelayR : RestCat
DelayR = record { 
  cat  = Kl DelayM; 
  rest = drest; 
  R1   = λ {_}{_}{f} → ext (dR1 {f = f});
  R2   = λ {_}{_}{_}{f}{g} → ext (dR2 {f = f} {g = g}); 
  R3   = λ {_}{_}{_}{f}{g} → ext (dR3 {f = f} {g = g}); 
  R4   = λ {_}{_}{_}{f}{g} → ext (dR4 {f = f} {g = g})}

-- Restriction product

open RestCat DelayR
open import RestrictionProducts DelayR
open import Totals DelayR
open import Monads
open Monad DelayM
open Tot

-- Useful equalities

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
dtr1-aux↓' (later dx) (later dz) (later dy) (later∼ p) (later↓ (later↓ q)) | .(later dw) | later∼ {._} {dw} r = later↓ (dtr1-aux↓' (♭ dx) (♭ dw) (♭ dy) (♭ r) q)

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
dtr2-aux↓' (later dx) (later dz) (later dy) (later∼ p) (later↓ (later↓ q)) | .(later dw) | later∼ {._} {dw} r = later↓ (dtr2-aux↓' (♭ dx) (♭ dw) (♭ dy) (♭ r) q)

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

DelayProd : (X Y : Set) → RestProd X Y
DelayProd X Y = record {
  W = X × Y;
  p₁ = dp₁;
  p₂ = dp₂;
  ⟨_,_⟩ = d⟨_,_⟩;
  tr1 = λ {Z}{f}{g} → ext (dtr1 {f = f} {g = g});
  tr2 = λ {Z}{f}{g} → ext (dtr2 {f = f} {g = g});
  uniq = {!!} }