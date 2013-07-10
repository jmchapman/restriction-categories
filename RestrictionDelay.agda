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
