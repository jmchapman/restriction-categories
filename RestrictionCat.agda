{-# OPTIONS --type-in-type #-}
module RestrictionCat where

open import Categories
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open ≅-Reasoning renaming (begin_ to proof_)
open import Function
open import Data.Product

record RestCat : Set where
  field cat  : Cat
  open  Cat cat
  field rest : ∀{A B} → Hom A B → Hom A A
        .R1   : ∀{A B}{f : Hom A B} → comp f (rest f) ≅ f 
        .R2   : ∀{A B C}{f : Hom A B}{g : Hom A C} →
               comp (rest f) (rest g) ≅ comp (rest g) (rest f)
        .R3   : ∀{A B C}{f : Hom A B}{g : Hom A C} →
               comp (rest g) (rest f) ≅ rest (comp g (rest f))
        .R4   : ∀{A B C}{f : Hom A B}{g : Hom B C} →
               comp (rest g) f ≅ comp f (rest (comp g f))


module Lemmata (X : RestCat) where
  open RestCat X
  open Cat cat
  open import Categories.Monos cat
  
  .lemii : ∀{A B}{f : Hom A B} → comp (rest f) (rest f) ≅ rest f
  lemii {f = f} = 
    proof
    comp (rest f) (rest f) 
    ≅⟨ R3 ⟩ 
    rest (comp f (rest f))
    ≅⟨ cong rest R1 ⟩ 
    rest f
    ∎

  .lemiii : ∀{A B}{f : Hom A B} → Mono f → rest f ≅ iden
  lemiii {f = f} p = p $
    proof
    comp f (rest f)
    ≅⟨ R1 ⟩ 
    f
    ≅⟨ sym idr ⟩ 
    comp f iden
    ∎

  .lemi : ∀{A B}{f : Hom A B} → rest (rest f) ≅ rest f
  lemi {f = f} = 
    proof
    rest (rest f)
    ≅⟨ cong rest (sym idl) ⟩ 
    rest (comp iden (rest f))
    ≅⟨ sym R3 ⟩ 
    comp (rest iden) (rest f)
    ≅⟨ cong (λ g → comp g (rest f)) (lemiii idmono) ⟩ 
    comp iden (rest f)
    ≅⟨ idl ⟩ 
    rest f
    ∎

  .lemiv : ∀{A B C}{f : Hom A B}{g : Hom B C} → 
          rest (comp g f) ≅ rest (comp (rest g) f)
  lemiv {f = f}{g = g} = 
    proof
    rest (comp g f) 
    ≅⟨ cong (λ f' → rest (comp g f')) (sym R1) ⟩ 
    rest (comp g (comp f (rest f))) 
    ≅⟨ cong rest (sym ass) ⟩ 
    rest (comp (comp g f) (rest f)) 
    ≅⟨ sym R3 ⟩ 
    comp (rest (comp g f)) (rest f) 
    ≅⟨ R2 ⟩ 
    comp (rest f) (rest (comp g f)) 
    ≅⟨ R3 ⟩ 
    rest (comp f (rest (comp g f))) 
    ≅⟨ cong rest (sym R4) ⟩ 
    rest (comp (rest g) f) 
    ∎

  _≤_ : ∀{A B} → Hom A B → Hom A B → Set
  f ≤ g = comp g (rest f) ≅ f

  -- antisymmetry
  .ex1 : ∀{A B}(f g : Hom A B) → f ≤ g → g ≤ f → f ≅ g
  ex1 f g p q = 
    proof 
    f 
    ≅⟨ sym p ⟩ 
    comp g (rest f)
    ≅⟨ cong (λ g' → comp g' (rest f)) (sym q) ⟩ 
    comp (comp f (rest g)) (rest f)
    ≅⟨ ass ⟩ 
    comp f (comp (rest g) (rest f))
    ≅⟨ cong (comp f) (sym R2) ⟩ 
    comp f (comp (rest f) (rest g))
    ≅⟨ sym ass ⟩ 
    comp (comp f (rest f)) (rest g)
    ≅⟨ cong (λ f' → comp f' (rest g)) R1 ⟩ 
    comp f (rest g)
    ≅⟨ q ⟩ 
    g 
    ∎



Trivial : Cat → RestCat
Trivial C = record { 
  cat  = C; 
  rest = λ _ → iden; 
  R1   = idr; 
  R2   = refl; --proof comp iden iden ∎;
  R3   = idr; 
  R4   = λ {_ _ _ f} →
   proof 
   comp iden f 
   ≅⟨ idl ⟩ 
   f 
   ≅⟨ sym idr ⟩ 
   comp f iden 
   ∎}
  where open Cat C

module Totals (X : RestCat) where
  open RestCat X
  open Lemmata X
  open Cat cat
  open import Categories.Monos
  open import Categories.Isos

  record Tot (A B : Obj) : Set where
    field hom : Hom A B 
          .tot : rest hom ≅ iden {A}

  open Tot

  .TotEq : ∀{A B}(f g : Tot A B) → hom f ≅ hom g → f ≅ g
  TotEq {A}{B} f g p = cong₂
    {_}
    {_}
    {_}
    {Hom A B}
    {λ hom → rest hom ≅ iden {A}}
    {λ _ _ → Tot A B}
    {hom f}
    {hom g}
    {tot f}
    {tot g}    
    (λ x y → record { hom = x; tot = y }) 
    p 
    (fixtypes'' refl)
--    (fixtypes (cong rest p) refl)

  identot : ∀{A} → Tot A A
  identot = record { hom = iden; tot = lemiii (idmono cat) } 

  comptot : ∀{A B C}(g : Tot B C)(f : Tot A B) → Tot A C
  comptot g f = record { 
    hom = comp (hom g) (hom f); 
    tot = 
      proof
      rest (comp (hom g) (hom f)) 
      ≅⟨ lemiv ⟩ 
      rest (comp (rest (hom g)) (hom f)) 
      ≅⟨ cong (λ h → rest (comp h (hom f))) (tot g) ⟩ 
      rest (comp iden (hom f))
      ≅⟨ cong rest idl ⟩ 
      rest (hom f)
      ≅⟨ tot f ⟩ 
      iden
      ∎}

  Total : Cat
  Total = record {
    Obj  = Obj; 
    Hom  = Tot;
    iden = identot;
    comp = comptot;
    idl  = λ{_}{_}{f} → TotEq (comptot identot f) f idl;
    idr  = λ{_}{_}{f} → TotEq (comptot f identot) f idr;
    ass  = λ{_}{_}{_}{_}{f}{g}{h} → 
      TotEq (comptot (comptot f g) h) (comptot f (comptot g h)) ass}

  .MonoTot : ∀{A B}(f : Tot A B) → Mono cat (hom f) → Mono Total f
  MonoTot f p {C}{g}{h} q = TotEq g h (p (cong hom q))

  .IsoTot : ∀{A B}(f : Tot A B) → Iso cat (hom f) → Iso Total f
  IsoTot f fiso = 
    let open Iso cat fiso renaming (inv to g; rinv to p; linv to q) 
        open Tot f renaming (hom to fhom)
        gt = record { 
          hom = g; 
          tot = iso→mono cat (fhom ,, q ,, p) 
                         (proof
                          comp g (rest g)
                          ≅⟨ R1 ⟩
                          g
                          ≅⟨ sym idr ⟩
                          comp g iden
                          ∎) }

    in gt  ,, 
     TotEq (comptot f gt) identot p ,,
     TotEq (comptot gt f) identot q

open import Functors

record RestFun (X Y : RestCat) : Set where
  open Cat
  open RestCat
  open Fun
  field fun   : Fun (cat X) (cat Y)
        .frest : ∀{A B}{f : Hom (cat X) A B} → 
                rest Y (HMap fun f) ≅ HMap fun (rest X f)

F : ∀{X} → Fun (Totals.Total X) (RestCat.cat X)
F {X} = record { 
  OMap  = id; 
  HMap  = hom; 
  fid   = refl;
  fcomp = refl}
  where open Totals X
        open Tot

RF : ∀{X} → RestFun (Trivial (Totals.Total X)) X
RF {X} = record { 
  fun   = F; 
  frest = λ {_ _ f} → tot f }
  where open Totals X
        open Tot

.RFFaithful : ∀{X} → Faithful (F {X})
RFFaithful {X} = λ {_} {_} {f} {g} → TotEq f g
  where open Totals X
        open Tot

