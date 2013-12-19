{-# OPTIONS --type-in-type #-}
module Restriction.Delay where

open import Coinduction
open import Categories
open import Monads
open import Categories.Functors
open import Monads.Kleisli
open import Categories.Sets
open import Utilities
open import Restriction.Cat
open import Monads.Delay

drest : ∀{X Y} → (X → Delay Y) → X → Delay X
drest f x = dmap proj₁ (str (x , f x))

qrest : ∀{X Y} → (X → QDelay Y) → X → QDelay X
qrest f x = qmap proj₁ (qstr (x , f x))

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

import Relation.Binary.EqReasoning

dR1 : ∀{X Y}{f : X → Delay Y}(x : X) → (dbind f ∘ (drest f)) x ≈ f x
dR1 {X}{Y}{f = f} x = 
  let open Monad DelayM 
      open Relation.Binary.EqReasoning 
        (record {Carrier = Delay Y;_≈_ = proj₁ ≈EqR;isEquivalence = proj₂ ≈EqR})
        renaming (begin_ to dproof_; _≡⟨⟩_ to _≈⟨⟩_; _∎ to _d∎) in
  dproof 
  dbind f (drest f x)
  ≈⟨⟩ 
  dbind f (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x)))
  ≈⟨ dbindcong1 f (sym≈ (dlaw3 (f x))) ⟩ 
  dbind f (dbind (dbind (now ∘ proj₁) ∘ (λ y → now (x , y))) (f x))
  ≈⟨⟩ 
  dbind f (dbind (λ _ → now x) (f x))
  ≈⟨ sym≈ (dlaw3 (f x)) ⟩ 
  dbind (λ _ → f x) (f x)
  ≈⟨ sym≈ lemma ⟩ 
  f x 
  d∎

dR2 : ∀{X Y Z}{f : X → Delay Y}{g : X → Delay Z}(x : X) → 
      (dbind (drest f) ∘ (drest g)) x ≈ (dbind (drest g) ∘ (drest f)) x
dR2 {X}{Y}{Z}{f}{g} x = 
  let open Monad DelayM
      open Relation.Binary.EqReasoning (record {Carrier      = Delay X;
                                                _≈_          = proj₁ ≈EqR;
                                               isEquivalence = proj₂ ≈EqR })
           renaming (begin_ to dproof_; _≡⟨⟩_ to _≈⟨⟩_; _∎ to _d∎) in 
      dproof
      dbind (drest f) (drest g x)
      ≈⟨⟩
      dbind (drest f) (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (g x)))
      ≈⟨ (dbindcong1 (drest f) (sym≈ (dlaw3 (g x)))) ⟩
      dbind (drest f) (dbind (λ _ → now x) (g x))
      ≈⟨ sym≈ (dlaw3 {f = λ _ → now x} {g = drest f} (g x)) ⟩
      dbind (λ _ → dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x))) (g x)
      ≈⟨ dbindcong2 (λ _ → sym≈ (dlaw3 {f = λ y → now (x , y)} {g = now ∘ proj₁} (f x))) (g x) ⟩
      dbind (λ _ → dbind (λ _ → now x) (f x)) (g x)
      ≈⟨ ∼→≈ (lemma2 {dy = f x} {dz = g x}) ⟩
      dbind (λ _ → dbind (λ _ → now x) (g x)) (f x)
      ≈⟨ dbindcong2 (λ _ → dlaw3 {f = λ y → now (x , y)} {g = now ∘ proj₁} (g x)) (f x) ⟩
      dbind (λ _ → dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (g x))) (f x)
      ≈⟨ dlaw3 {f = λ _ → now x} {g = drest g} (f x) ⟩
      dbind (drest g) (dbind (λ _ → now x) (f x))
      ≈⟨ (dbindcong1 (drest g) (dlaw3 (f x))) ⟩
      dbind (drest g) (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x)))
      ≈⟨⟩
      dbind (drest g) (drest f x)
      d∎

dR3 : ∀{X Y Z}{f : X → Delay Y}{g : X → Delay Z}(x : X) → 
      (dbind (drest g) ∘ (drest f)) x ≈ drest (dbind g ∘ (drest f)) x
dR3 {X}{Y}{Z}{f}{g} x = 
  let open Monad DelayM
      open Relation.Binary.EqReasoning (record {Carrier      = Delay X;
                                                _≈_          = proj₁ ≈EqR;
                                               isEquivalence = proj₂ ≈EqR })
           renaming (begin_ to dproof_; _≡⟨⟩_ to _≈⟨⟩_; _∎ to _d∎) in 
  dproof
  dbind (drest g) (drest f x)
  ≈⟨⟩
  dbind (drest g) (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x)))
  ≈⟨ dbindcong1 (drest g) (sym≈ (dlaw3 (f x))) ⟩
  dbind (drest g) (dbind (λ _ → now x) (f x))
  ≈⟨ sym≈ (dlaw3 {f = λ _ → now x} {g = drest g} (f x)) ⟩
  dbind (λ _ → dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (g x))) (f x)
  ≈⟨ dbindcong2 (λ _ → sym≈ (dlaw3 {f = λ y → now (x , y)} {g = now ∘ proj₁} (g x))) (f x) ⟩
  dbind (λ _ → dbind (λ _ → now x) (g x)) (f x)
  ≈⟨ dlaw3 (f x) ⟩
  dbind (λ _ → now x) (dbind (λ _ → g x) (f x))
  ≈⟨ dlaw3 (dbind (λ _ → g x) (f x)) ⟩
  dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (dbind (λ _ → g x) (f x)))
  ≈⟨ dbindcong1 (now ∘ proj₁) (dbindcong1 (λ y → now (x , y)) (dlaw3 {f = λ _ → now x} {g = g} (f x))) ⟩
  dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (dbind g (dbind (λ _ → now x) (f x))))
  ≈⟨ dbindcong1 (now ∘ proj₁) (dbindcong1 (λ y → now (x , y)) (dbindcong1 g (dlaw3 (f x)))) ⟩
  dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (dbind g (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (f x)))))
  ≈⟨⟩
  drest (dbind g ∘ (drest f)) x
  d∎

dR4 : ∀{X Y Z}{f : X → Delay Y}{g : Y → Delay Z}(x : X) →
      (dbind (drest g) ∘ f) x ≈ (dbind f ∘ (drest (dbind g ∘ f))) x
dR4 {X}{Y}{Z}{f}{g} x = 
  let open Monad DelayM
      open Relation.Binary.EqReasoning (record {Carrier      = Delay Y;
                                                _≈_          = proj₁ ≈EqR;
                                               isEquivalence = proj₂ ≈EqR })
           renaming (begin_ to dproof_; _≡⟨⟩_ to _≈⟨⟩_; _∎ to _d∎) in 
  dproof
  dbind (drest g) (f x)
  ≈⟨⟩
  dbind (λ y → dbind (now ∘ proj₁) (dbind (λ z → now (y , z)) (g y))) (f x)
  ≈⟨ dbindcong2 (λ y → sym≈ (dlaw3 (g y))) (f x) ⟩
  dbind (λ y → dbind (λ _ → now y) (g y)) (f x)
  ≈⟨ lemma3 {dy = f x} {g = g} ⟩
  dbind (λ y → dbind (λ _ → f x) (g y)) (f x)
  ≈⟨ dlaw3 (f x) ⟩ 
  dbind (λ _ → f x) (dbind g (f x))
  ≈⟨ dlaw3 (dbind g (f x)) ⟩ 
  dbind f (dbind (λ _ → now x) (dbind g (f x)))
  ≈⟨ dbindcong1 f (dlaw3 (dbind g (f x))) ⟩
  dbind f (dbind (now ∘ proj₁) (dbind (λ y → now (x , y)) (dbind g (f x))))
  ≈⟨⟩
  dbind f (drest (dbind g ∘ f) x)
  d∎


{-

DelayR : RestCat
DelayR = let open ≅-Reasoning renaming (begin_ to proof_) in
  record { 
    cat  = Kl DelayM; 
    rest = λ f x → abs (drest (rep ∘ f) x);
    R1   = λ {A} {B} {f} → ext λ x → 
      proof
      abs (dbind (rep ∘ f) (rep (abs (drest (rep ∘ f) x))))
      ≅⟨ ax1 _ _ (dbindcong1 (rep ∘ f) (ax3 _)) ⟩
      abs (dbind (rep ∘ f) (drest (rep ∘ f) x))
      ≅⟨ ax1 _ _ (dR1 {f = rep ∘ f} x) ⟩
      abs (rep (f x))
      ≅⟨ ax2 _ ⟩
      f x ∎;
    R2   = λ {_}{_}{_}{f}{g} → ext λ x → 
      proof
      abs (dbind (rep ∘ abs ∘ (drest (rep ∘ f))) (rep (abs (drest (rep ∘ g) x))))
      ≅⟨ ax1 _ _ (dbindcong2 (λ x → ax3 (drest (rep ∘ f) x)) (rep (abs (drest (rep ∘ g) x)))) ⟩
      abs (dbind (drest (rep ∘ f)) (rep (abs (drest (rep ∘ g) x))))
      ≅⟨ ax1 _ _ (dbindcong1 (drest (rep ∘ f)) (ax3 _)) ⟩
      abs (dbind (drest (rep ∘ f)) (drest (rep ∘ g) x))
      ≅⟨ ax1 _ _ (dR2 {f = rep ∘ f} {g = rep ∘ g} x) ⟩
      abs (dbind (drest (rep ∘ g)) (drest (rep ∘ f) x))
      ≅⟨ ax1 _ _ (sym≈ (dbindcong1 (drest (rep ∘ g)) (ax3 _))) ⟩
      abs (dbind (drest (rep ∘ g)) (rep (abs (drest (rep ∘ f) x))))
      ≅⟨ ax1 _ _ (sym≈ (dbindcong2 (λ x → ax3 (drest (rep ∘ g) x)) (rep (abs (drest (rep ∘ f) x))))) ⟩
      abs (dbind (rep ∘ abs ∘ (drest (rep ∘ g))) (rep (abs (drest (rep ∘ f) x))))
      ∎;
    R3   = R3; --λ {_}{_}{_}{f}{g} → ext (dR3 {f = f} {g = g}); 
    R4   = R4} --λ {_}{_}{_}{f}{g} → ext (dR4 {f = f} {g = g})}

-}