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
open import Relation.Binary
open IsEquivalence renaming (refl to irefl; sym to isym; trans to itrans)

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

dR1 : ∀{X Y}{f : X → Delay Y}(x : X) → dbind f (drest f x) ≈ f x
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

.qR1 : ∀{X Y}{f : X → QDelay Y}(x : X) → qbind f (qrest f x) ≅ f x
qR1 {X}{Y}{f} x = 
  proof 
  qbind f (qrest f x)
  ≡⟨⟩ 
  qbind f (qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (f x)))
  ≅⟨ cong (λ g → qbind f (g (f x))) (sym qlaw3) ⟩
  qbind f (qbind (qbind (abs ∘ now ∘ proj₁) ∘ (abs ∘ now ∘ (λ y → (x , y)))) (f x))
  ≅⟨ cong (λ g → qbind f (qbind g (f x))) (ext (λ _ → qbindabsabs)) ⟩
  qbind f (qbind (λ y → abs (dbind (now ∘ proj₁) (now (x , y)))) (f x))
  ≡⟨⟩
  qbind f (qbind (λ _ → abs (now x)) (f x))
  ≅⟨ cong (λ g → g (f x)) (sym qlaw3) ⟩
  qbind (λ _ → qbind f (abs (now x))) (f x)
  ≅⟨ cong (λ y → qbind (λ _ → y x) (f x)) qlaw2 ⟩
  qbind (λ _ → f x) (f x)
  ≅⟨ lift {Y = λ y → qbind (λ _ → y) y ≅ y} 
          (λ y → 
            proof
            qbind (λ _ → abs y) (abs y)
            ≅⟨ qbindabsabs ⟩
            abs (dbind (λ _ → y) y)
            ≅⟨ ax1 _ _ (sym≈ lemma) ⟩
            abs y
            ∎) 
          (λ p → fixtypes'' (ax1 _ _ p)) 
          (f x) ⟩ 
  f x
  ∎ 

dR2 : ∀{X Y Z}{f : X → Delay Y}{g : X → Delay Z}(x : X) → 
      dbind (drest f) (drest g x) ≈ dbind (drest g) (drest f x)
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
      ≈⟨ dbindcong1 (drest f) (sym≈ (dlaw3 (g x))) ⟩
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

.qR2 : ∀{X Y Z}{f : X → QDelay Y}{g : X → QDelay Z}(x : X) → 
      qbind (qrest f) (qrest g x) ≅ qbind (qrest g) (qrest f x)
qR2 {X}{Y}{Z}{f}{g} x = 
  proof
  qbind (qrest f) (qrest g x)
  ≡⟨⟩
  qbind (qrest f) (qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (g x)))
  ≅⟨ cong (λ h → qbind (qrest f) (h (g x))) (sym qlaw3) ⟩
  qbind (qrest f) (qbind (qbind (abs ∘ now ∘ proj₁) ∘ (abs ∘ now ∘ (λ y → (x , y)))) (g x))
  ≅⟨ cong (λ h → qbind (qrest f) (qbind h (g x))) (ext (λ _ → qbindabsabs)) ⟩
  qbind (qrest f) (qbind (λ y → abs (dbind (now ∘ proj₁) (now (x , y)))) (g x))
  ≡⟨⟩
  qbind (qrest f) (qbind (λ _ → abs (now x)) (g x))
  ≅⟨ cong (λ h → h (g x)) (sym qlaw3) ⟩
  qbind (λ _ → qbind (qrest f) (abs (now x))) (g x)
  ≅⟨ cong (λ y → qbind (λ _ → y x) (g x)) qlaw2 ⟩
  qbind (λ _ → qrest f x) (g x)
  ≡⟨⟩
  qbind (λ _ → qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (f x))) (g x)
  ≅⟨ cong (λ h → qbind (λ _ → h (f x)) (g x)) (sym qlaw3) ⟩
  qbind (λ _ → qbind (λ y → qbind (abs ∘ now ∘ proj₁) (abs (now (x , y)))) (f x)) (g x)
  ≅⟨ cong (λ h → qbind (λ _ → qbind h (f x)) (g x)) (ext (λ _ → qbindabsabs)) ⟩
  qbind (λ _ → qbind (λ y → abs (dbind (now ∘ proj₁) (now (x , y)))) (f x)) (g x)
  ≡⟨⟩
  qbind (λ _ → qbind (λ _ → abs (now x)) (f x)) (g x)
  ≅⟨ lift
       {Y =
        λ y →
          qbind (λ _ → qbind (λ _ → abs (now x)) y) (g x) ≅
          qbind (λ _ → qbind (λ _ → abs (now x)) (g x)) y}
       (λ y → 
         proof 
         qbind (λ _ → qbind (abs ∘ (λ _ → now x)) (abs y)) (g x)
         ≅⟨ cong (λ h → qbind h (g x)) (ext (λ _ → qbindabsabs)) ⟩
         qbind (λ _ → abs (dbind (λ _ → now x) y)) (g x)
         ≅⟨ lift
              {Y =
               λ z →
                 qbind (λ _ → abs (dbind (λ _ → now x) y)) z ≅
                 qbind (λ _ → qbind (λ _ → abs (now x)) z) (abs y)}
              (λ z → 
                proof
                qbind (λ _ → abs (dbind (λ _ → now x) y)) (abs z)
                ≅⟨ qbindabsabs ⟩
                abs (dbind (λ _ → dbind (λ _ → now x) y) z)
                ≅⟨ ax1 _ _ (∼→≈ (lemma2 {dy = y} {dz = z})) ⟩
                abs (dbind (λ _ → dbind (λ _ → now x) z) y)
                ≅⟨ sym qbindabsabs ⟩
                qbind (λ _ → abs (dbind (λ _ → now x) z)) (abs y)
                ≅⟨ cong (λ h → qbind h (abs y)) (ext (λ _ → sym qbindabsabs)) ⟩
                qbind (λ _ → qbind (abs ∘ (λ _ → now x)) (abs z)) (abs y)
                ∎) 
              (λ r → fixtypes' (cong (qbind (λ _ → abs (dbind (λ _ → now x) y))) (ax1 _ _ r))) 
              (g x) ⟩
         qbind (λ _ → qbind (abs ∘ (λ _ → now x)) (g x)) (abs y)
         ∎)
       (λ r →
            fixtypes''
            (cong (qbind (λ _ → qbind (abs ∘ (λ _ → now x)) (g x)))
             (ax1 _ _ r))) 
       (f x) ⟩
  qbind (λ _ → qbind (λ _ → abs (now x)) (g x)) (f x)
  ≡⟨⟩
  qbind (λ _ → qbind (λ y → abs (dbind (now ∘ proj₁) (now (x , y)))) (g x)) (f x)
  ≅⟨ cong (λ h → qbind (λ _ → qbind h (g x)) (f x)) (ext (λ _ → sym qbindabsabs)) ⟩
  qbind (λ _ → qbind (λ y → qbind (abs ∘ now ∘ proj₁) (abs (now (x , y)))) (g x)) (f x)
  ≅⟨ cong (λ h → qbind (λ _ → h (g x)) (f x)) qlaw3 ⟩
  qbind (λ _ → qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (g x))) (f x)
  ≡⟨⟩
  qbind (λ _ → qrest g x) (f x)
  ≅⟨ cong (λ y → qbind (λ _ → y x) (f x)) (sym qlaw2) ⟩
  qbind (λ _ → qbind (qrest g) (abs (now x))) (f x)
  ≅⟨ cong (λ h → h (f x)) qlaw3 ⟩
  qbind (qrest g) (qbind (λ _ → abs (now x)) (f x))
  ≡⟨⟩
  qbind (qrest g) (qbind (λ y → abs (dbind (now ∘ proj₁) (now (x , y)))) (f x))
  ≅⟨ cong (λ h → qbind (qrest g) (qbind h (f x))) (ext (λ _ → sym qbindabsabs)) ⟩
  qbind (qrest g) (qbind (qbind (abs ∘ now ∘ proj₁) ∘ (abs ∘ now ∘ (λ y → (x , y)))) (f x))
  ≅⟨ cong (λ h → qbind (qrest g) (h (f x))) qlaw3 ⟩
  qbind (qrest g) (qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (f x)))
  ≡⟨⟩
  qbind (qrest g) (qrest f x)
  ∎
  
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

.qR3 : ∀{X Y Z}{f : X → QDelay Y}{g : X → QDelay Z}(x : X) → 
       qbind (qrest g) (qrest f x) ≅ qrest (qbind g ∘ (qrest f)) x
qR3 {X}{Y}{Z}{f}{g} x = 
  proof
  qbind (qrest g) (qrest f x)
  ≡⟨⟩
  qbind (qrest g) (qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (f x)))
  ≅⟨ cong (λ h → qbind (qrest g) (h (f x))) (sym qlaw3) ⟩
  qbind (qrest g) (qbind (qbind (abs ∘ now ∘ proj₁) ∘ (abs ∘ now ∘ (λ y → (x , y)))) (f x))
  ≅⟨ cong (λ h → qbind (qrest g) (qbind h (f x))) (ext (λ _ → qbindabsabs)) ⟩
  qbind (qrest g) (qbind (λ y → abs (dbind (now ∘ proj₁) (now (x , y)))) (f x))
  ≡⟨⟩
  qbind (qrest g) (qbind (λ _ → abs (now x)) (f x))
  ≅⟨ cong (λ h → h (f x)) (sym qlaw3) ⟩
  qbind (λ _ → qbind (qrest g) (abs (now x))) (f x)
  ≅⟨ cong (λ y → qbind (λ _ → y x) (f x)) qlaw2 ⟩
  qbind (λ _ → qrest g x) (f x)
  ≡⟨⟩
  qbind (λ _ → qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (g x))) (f x)
  ≅⟨ cong (λ h → qbind (λ _ → h (g x)) (f x)) (sym qlaw3) ⟩
  qbind (λ _ → qbind (λ y → qbind (abs ∘ now ∘ proj₁) (abs (now (x , y)))) (g x)) (f x)
  ≅⟨ cong (λ h → qbind (λ _ → qbind h (g x)) (f x)) (ext (λ _ → qbindabsabs)) ⟩
  qbind (λ _ → qbind (λ y → abs (dbind (now ∘ proj₁) (now (x , y)))) (g x)) (f x)
  ≡⟨⟩
  qbind (λ _ → qbind (λ _ → abs (now x)) (g x)) (f x)
  ≅⟨ cong (λ h → h (f x)) qlaw3 ⟩
  qbind (λ _ → abs (now x)) (qbind (λ _ → g x) (f x))
  ≡⟨⟩
  qbind (λ y → abs (dbind (now ∘ proj₁) (now (x , y)))) (qbind (λ _ → g x) (f x))
  ≅⟨ cong (λ h → qbind h (qbind (λ _ → g x) (f x))) (ext (λ _ → sym qbindabsabs)) ⟩
  qbind (λ y → qbind (abs ∘ now ∘ proj₁) (abs (now (x , y)))) (qbind (λ _ → g x) (f x))
  ≅⟨ cong (λ h → h (qbind (λ _ → g x) (f x))) qlaw3 ⟩
  qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (qbind (λ _ → g x) (f x)))
  ≅⟨ cong (λ h → qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (qbind (λ _ → h x) (f x)))) (sym qlaw2) ⟩
  qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (qbind (λ _ → qbind g (abs (now x))) (f x)) )
  ≅⟨ cong (λ h → qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (h (f x)))) qlaw3 ⟩
  qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (qbind g (qbind (λ _ → abs (now x)) (f x))))
  ≡⟨⟩
  qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (qbind g (qbind (λ y → abs (dbind (now ∘ proj₁) (now (x , y)))) (f x))))
  ≅⟨ cong (λ h → qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (qbind g (qbind h (f x))))) (ext (λ _ → sym qbindabsabs))  ⟩
  qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (qbind g (qbind (qbind (abs ∘ now ∘ proj₁) ∘ (abs ∘ now ∘ (λ y → (x , y)))) (f x))))
  ≅⟨ cong (λ h → qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (qbind g (h (f x))))) qlaw3 ⟩
  qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (qbind g (qbind (abs ∘ now ∘ proj₁) (qbind (λ y → abs (now (x , y))) (f x)))))
  ≡⟨⟩
  qrest (qbind g ∘ (qrest f)) x
  ∎

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
DelayR = 
  record { 
    cat  = Kl DelayM; 
    rest = qrest;
    R1   = {!!};
    R2   = {!!};
    R3   = {!!}; 
    R4   = {!!}} 
-}
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