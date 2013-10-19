
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




