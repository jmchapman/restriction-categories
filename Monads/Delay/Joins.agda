

module Monads.Delay.Joins where

open import Coinduction
open import Categories
open import Monads.Kleisli
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open ≅-Reasoning renaming (begin_ to proof_)
open import Monads.Delay
open Cat (Kl DelayM)
open import RestrictionDelay
open import RestrictionCat
open RestCat DelayR
open import Order DelayR
open Joins

-- Joins


_d⌣_ : ∀{X Y}(f g : X → Delay Y) → Set
_d⌣_ {X} f g = ∀ x → dcomp (f x) (g x) ≈ dcomp (g x) (f x)

{-
d⌣→⌣' : ∀{X Y}{f g : X → Delay Y} → f d⌣ g → ∀ x → 
        dbind g (drest f x) ≅ dbind f (drest g x)
d⌣→⌣' {f = f}{g = g} p x = 
  proof
  dbind g (drest f x) 
  ≅⟨ cong (dbind g) (drest≅ x f) ⟩
  dbind g (dbind (λ z → now x) (f x))
  ≅⟨ sym (compdrest {f = g} {g = f} x) ⟩
  dbind (λ _ → g x) (f x)
  ≅⟨ quotient (sym≈ (dcomp≈dbind {_}{_}{f x})) ⟩
  dcomp (f x) (g x)
  ≅⟨ quotient (p x) ⟩
  dcomp (g x) (f x)
  ≅⟨ quotient (dcomp≈dbind {_}{_}{g x}) ⟩
  dbind (λ _ → f x) (g x)
  ≅⟨ compdrest {f = f} {g = g} x ⟩
  dbind f (dbind (λ z → now x) (g x))
  ≅⟨ sym (cong (dbind f) (drest≅ x g)) ⟩
  dbind f (drest g x)
  ∎

d⌣→⌣ : ∀{X Y}{f g : X → Delay Y} → f d⌣ g → f ⌣ g
d⌣→⌣ {f = f} p = ext (d⌣→⌣' {f = f} p)

⌣→d⌣ : ∀{X Y}{f g : X → Delay Y} → f ⌣ g → f d⌣ g
⌣→d⌣ {f = f}{g = g} p x = 
  subst 
    (_≈_ (dcomp (f x) (g x))) 
    (proof 
     dcomp (f x) (g x) 
     ≅⟨ quotient (dcomp≈dbind {_}{_}{f x}) ⟩
     dbind (λ _ → g x) (f x)
     ≅⟨ compdrest {f = g} {g = f} x ⟩
     dbind g (dbind (λ z → now x) (f x))
     ≅⟨ sym (cong (dbind g) (drest≅ x f)) ⟩
     dbind g (drest f x)
     ≅⟨ cong (λ h → h x) p ⟩ 
     dbind f (drest g x) 
     ≅⟨ cong (dbind f) (drest≅ x g) ⟩
     dbind f (dbind (λ z → now x) (g x))
     ≅⟨ sym (compdrest {f = f} {g = g} x) ⟩
     dbind (λ _ → f x) (g x)
     ≅⟨ quotient (sym≈ (dcomp≈dbind {_}{_}{g x})) ⟩
     dcomp (g x) (f x)
     ∎)
    refl≈

djoin-aux : ∀{X}(dx dy : Delay X) → dcomp dx dy ≈ dcomp dy dx → Delay X
djoin-aux (now x) (now .x) (↓≈ now↓ now↓) = now x
djoin-aux (now x) (later dy) p = now x
djoin-aux (later dx) (now y) p = now y
djoin-aux (later dx) (later dy) (↓≈ (later↓ {y = y} p) (later↓ q)) = now y
djoin-aux (later dx) (later dy) (later≈ p) = 
  later (♯ (djoin-aux (♭ dx) (♭ dy) (♭ p)))

djoin : {X Y : Set}(f g : X → Delay Y) → f d⌣ g → X → Delay Y
djoin f g p x = djoin-aux (f x) (g x) (p x)

djoin-comm-aux : ∀{X}{dx dy : Delay X}{p : dcomp dx dy ≈ dcomp dy dx} →
                 djoin-aux dx dy p ≈ djoin-aux dy dx (sym≈ p)
djoin-comm-aux {X} {now x} {now .x} {↓≈ now↓ now↓} = ↓≈ now↓ now↓
djoin-comm-aux {X} {now x} {later dy} = ↓≈ now↓ now↓
djoin-comm-aux {X} {later dx} {now x} = ↓≈ now↓ now↓
djoin-comm-aux {X} {later dx} {later dy} {↓≈ (later↓ p) (later↓ q)} = 
  ↓≈ now↓ now↓
djoin-comm-aux {X} {later dx} {later dy} {later≈ p} = 
  later≈ (♯ djoin-comm-aux {dx = ♭ dx})

djoin-comm : {X Y : Set}{f g : X → Delay Y}{p : f d⌣ g}(x : X) →
             djoin f g p x ≈ djoin g f (sym≈ ∘ p) x
djoin-comm {X}{Y}{f}{g} x = djoin-comm-aux {Y}{f x}{g x}

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
  ≅⟨ quotient (∼→≈ (dJn1a-aux {_} {f x} {g x} {p x})) ⟩
  f x
  ∎)

dJn1b : ∀{X Y}{f g : X → Delay Y}{p : f d⌣ g} → g ≤ djoin f g p
dJn1b {f = f}{g = g}{p = p} = 
  trans (cong (λ y → comp y (rest g)) 
              (ext (λ x → quotient (djoin-comm {f = f}{g = g}{p = p} x)))) 
        (dJn1a {_} {_} {g} {f} {sym≈ ∘ p})

dJn2-aux : ∀{X}{dx dy dz : Delay X}{p : dcomp dx dy ≈ dcomp dy dx} →
           dcomp dx dz ≈ dx → dcomp dy dz ≈ dy → 
           dcomp (djoin-aux dx dy p) dz ≈ djoin-aux dx dy p
dJn2-aux {X} {now x} {now .x} {dz} {↓≈ now↓ now↓} q r = r
dJn2-aux {X} {now x} {later dy} q r = q
dJn2-aux {X} {later dx} {now x} q r = r
dJn2-aux {X} {later dx} {later dy} {now x} {↓≈ (later↓ p) (later↓ p')} (↓≈ (later↓ q) (later↓ q')) (↓≈ (later↓ r) (later↓ r')) with dcomp↓snd {_}{_}{♭ dy} r
dJn2-aux {X} {later dx} {later dy} {now x} {↓≈ (later↓ p) (later↓ p')} (↓≈ (later↓ q) (later↓ q')) (↓≈ (later↓ r) (later↓ r')) | now↓ with
  unique↓ r' (dcomp↓snd {_} {_} {♭ dx} p)
dJn2-aux {X} {later dx} {later dy} {now y} {↓≈ (later↓ p) (later↓ p')} (↓≈ (later↓ q) (later↓ q')) (↓≈ (later↓ r) (later↓ r')) | now↓ | refl = ↓≈ now↓ now↓
dJn2-aux {X} {later dx} {later dy} {now x} {↓≈ (later↓ p) (later↓ p')} (↓≈ (later↓ q) (later↓ q')) (later≈ r) with 
  dcomp↓snd {_} {_} {♭ dy} (≈↓ (sym≈ (♭ r)) (dcomp↓snd {_} {_} {♭ dx} p))
dJn2-aux {X} {later dx} {later dy} {now x} {↓≈ (later↓ p) (later↓ p')} (↓≈ (later↓ q) (later↓ q')) (later≈ r) | now↓ = ↓≈ now↓ now↓
dJn2-aux {X} {later dx} {later dy} {now x} {↓≈ (later↓ p) (later↓ p')} (later≈ q) r with
  dcomp↓snd {_} {_} {♭ dx} (≈↓ (sym≈ (♭ q)) (dcomp↓snd {_} {_} {♭ dy} p'))
dJn2-aux {X} {later dx} {later dy} {now x} {↓≈ (later↓ p) (later↓ p')} (later≈ q) r | now↓ = ↓≈ now↓ now↓
dJn2-aux {X} {later dx} {later dy} {later dz} {↓≈ (later↓ p) (later↓ p')} (↓≈ (later↓ q) (later↓ q')) r with
  unique↓ (dcomp↓snd {_} {_} {♭ dy} p') q'
dJn2-aux {X} {later dx} {later dy} {later dz} {↓≈ (later↓ p) (later↓ p')} (↓≈ (later↓ q) (later↓ q')) r | refl = ↓≈ (later↓ (dcomp↓snd {_} {_} {♭ dx} q)) now↓
dJn2-aux {X} {later dx} {later dy} {later dz} {↓≈ (later↓ p) (later↓ p')} (later≈ q) r with 
  dcomp↓snd {_} {_} {♭ dx} (≈↓ (sym≈ (♭ q)) (dcomp↓snd {_} {_} {♭ dy} p'))
... | s = ↓≈ (later↓ s) now↓
dJn2-aux {X} {later dx} {later dy} {now x} {later≈ p} (↓≈ (later↓ q) (later↓ q')) (↓≈ (later↓ r) (later↓ r')) = later≈ (♯ (dJn2-aux (↓≈ q q') (↓≈ r r')))
dJn2-aux {X} {later dx} {later dy} {now x} {later≈ p} (↓≈ (later↓ q) (later↓ q')) (later≈ r) = later≈ (♯ (dJn2-aux (↓≈ q q') (♭ r)))
dJn2-aux {X} {later dx} {later dy} {now x} {later≈ p} (later≈ q) (↓≈ (later↓ r) (later↓ r')) = later≈ (♯ (dJn2-aux (♭ q) (↓≈ r r')))
dJn2-aux {X} {later dx} {later dy} {now x} {later≈ p} (later≈ q) (later≈ r) = later≈ (♯ (dJn2-aux (♭ q) (♭ r)))
dJn2-aux {X} {later dx} {later dy} {later dz} {later≈ p} (↓≈ (later↓ q) (later↓ q')) (↓≈ (later↓ r) (later↓ r')) = later≈ (♯ (dJn2-aux (↓≈ q q') (↓≈ r r')))
dJn2-aux {X} {later dx} {later dy} {later dz} {later≈ p} (↓≈ (later↓ q) (later↓ q')) (later≈ r) = later≈ (♯ (dJn2-aux (↓≈ q q') (♭ r)))
dJn2-aux {X} {later dx} {later dy} {later dz} {later≈ p} (later≈ q) (↓≈ (later↓ r) (later↓ r')) = later≈ (♯ (dJn2-aux (♭ q) (↓≈ r r')))
dJn2-aux {X} {later dx} {later dy} {later dz} {later≈ p} (later≈ q) (later≈ r) = later≈ (♯ (dJn2-aux (♭ q) (♭ r)))

dJn2 : {X Y : Set}{f g h : X → Delay Y}{p : f d⌣ g} → f ≤ h → g ≤ h → 
       djoin f g p ≤ h
dJn2 {f = f}{g = g}{h = h}{p = p} q r = ext (λ x → 
  let q' : dcomp (f x) (h x) ≈ f x
      q' = 
        subst 
          (_≈_ (dcomp (f x) (h x))) 
          (proof
           dcomp (f x) (h x)
           ≅⟨ quotient (dcomp≈dbind {_}{_}{f x}) ⟩
           dbind (λ _ → h x) (f x)
           ≅⟨ compdrest {f = h} {g = f} x ⟩
           dbind h (dbind (λ z → now x) (f x))
           ≅⟨ sym (cong (dbind h) (drest≅ x f)) ⟩
           dbind h (drest f x)
           ≅⟨ cong (λ f' → f' x) q ⟩
           f x
           ∎)
          refl≈

      r' : dcomp (g x) (h x) ≈ g x
      r' = 
        subst 
          (_≈_ (dcomp (g x) (h x))) 
          (proof
           dcomp (g x) (h x)
           ≅⟨ quotient (dcomp≈dbind {_}{_}{g x}) ⟩
           dbind (λ _ → h x) (g x)
           ≅⟨ compdrest {f = h} {g = g} x ⟩
           dbind h (dbind (λ z → now x) (g x))
           ≅⟨ sym (cong (dbind h) (drest≅ x g)) ⟩
           dbind h (drest g x)
           ≅⟨ cong (λ f' → f' x) r ⟩
           g x
           ∎)
          refl≈
  in 
    proof
    dbind h (drest (djoin f g p) x)
    ≅⟨ cong (dbind h) (drest≅ x (djoin f g p)) ⟩
    dbind h (dbind (λ _ → now x) (djoin f g p x))
    ≅⟨ sym (compdrest {f = h} {g = djoin f g p} x) ⟩
    dbind (λ _ → h x) (djoin f g p x)
    ≅⟨ quotient (sym≈ (dcomp≈dbind {_}{_}{djoin f g p x})) ⟩
    dcomp (djoin f g p x) (h x)
    ≅⟨ quotient (dJn2-aux {dx = f x}{dy = g x} q' r') ⟩
    djoin f g p x
    ∎)

DelayJoin : Join
DelayJoin = record { 
  _∨_∣_ = λ f g p → djoin f g (⌣→d⌣ {f = f} p);
  Jn1a = dJn1a;
  Jn1b = λ {_}{_}{f} → dJn1b {f = f};
  Jn2 = dJn2; 
  Jn3 = {!!} }
-}