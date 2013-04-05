{-# OPTIONS --type-in-type #-}
module RestrictionCat where

open import Categories
open import Relation.Binary.HeterogeneousEquality
open import Equality
open ≅-Reasoning renaming (begin_ to proof_)
open import Function
open import Data.Product

record RestCat : Set where
  field cat  : Cat
  open  Cat cat
  field rest : ∀{A B} → Hom A B → Hom A A
        R1   : ∀{A B}{f : Hom A B} → comp f (rest f) ≅ f 
        R2   : ∀{A B C}{f : Hom A B}{g : Hom A C} →
               comp (rest f) (rest g) ≅ comp (rest g) (rest f)
        R3   : ∀{A B C}{f : Hom A B}{g : Hom A C} →
               comp (rest g) (rest f) ≅ rest (comp g (rest f))
        R4   : ∀{A B C}{f : Hom A B}{g : Hom B C} →
               comp (rest g) f ≅ comp  f (rest (comp g f))


module Lemmata (X : RestCat) where
  open RestCat X
  open Cat cat
  open Monos cat
  
  lemii : ∀{A B}{f : Hom A B} → comp (rest f) (rest f) ≅ rest f
  lemii {f = f} = 
    proof
    comp (rest f) (rest f) 
    ≅⟨ R3 ⟩ 
    rest (comp f (rest f))
    ≅⟨ cong rest R1 ⟩ 
    rest f
    ∎

  lemiii : ∀{A B}{f : Hom A B} → Mono f → rest f ≅ iden
  lemiii {f = f} p = p $
    proof
    comp f (rest f)
    ≅⟨ R1 ⟩ 
    f
    ≅⟨ sym idr ⟩ 
    comp f iden
    ∎

  lemi : ∀{A B}{f : Hom A B} → rest (rest f) ≅ rest f
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

  lemiv : ∀{A B C}{f : Hom A B}{g : Hom B C} → 
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
  ex1 : ∀{A B}(f g : Hom A B) → f ≤ g → g ≤ f → f ≅ g
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
  open Monos cat

  record Tot (A B : Obj) : Set where
    field hom : Hom A B 
          tot : rest hom ≅ iden {A}

  open Tot

  TotEq : ∀{A B}{f g : Tot A B} → hom f ≅ hom g → f ≅ g
  TotEq {A}{B}{f}{g} p = cong₂
    {_}
    {_}
    {_}
    {Hom A B}
    {λ hom → rest hom ≅ iden {A}}
    {λ _ _ → Tot A B}
    (λ x y → record { hom = x; tot = y }) p 
    (fixtypes (cong rest p) refl)

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

  Totals : Cat
  Totals = record {
    Obj  = Obj; 
    Hom  = Tot;
    iden = record { hom = iden; tot = lemiii idmono };
    comp = comptot;
    idl  = TotEq idl;
    idr  = TotEq idr;
    ass  = TotEq ass}

{-  
  TotalsR : RestCat
  TotalsR = record { 
    cat  = Totals; 
    rest = λ _ → record {hom = iden; 
                         tot = Lemmata.lemiii X (Monos.idmono cat)};
    R1   = TotEq idr;
    R2   = TotEq refl;
    R3   = TotEq idr;
    R4   = TotEq (trans idl (sym idr))}

  TotalsR : RestCat
  TotalsR = record { 
    cat  = Totals; 
    rest = λ f → record { 
      hom = rest (hom f); 
      tot = 
        proof
        rest (rest (hom f))
        ≅⟨ lemi ⟩ 
        rest (hom f)
        ≅⟨ tot f ⟩ 
        iden
        ∎};
    R1   = TotEq R1;
    R2   = TotEq R2;
    R3   = TotEq R3;
    R4   = TotEq R4}
-}

open import Functors

record RestFun (X Y : RestCat) : Set where
  open Cat
  open RestCat
  open Fun
  field fun   : Fun (cat X) (cat Y)
        frest : ∀{A B}{f : Hom (cat X) A B} → 
                rest Y (HMap fun f) ≅ HMap fun (rest X f)

F : ∀{X} → Fun (Totals.Totals X) (RestCat.cat X)
F {X} = record { 
  OMap  = id; 
  HMap  = hom; 
  fid   = refl;
  fcomp = refl}
  where open Totals X
        open Tot

RF : ∀{X} → RestFun (Trivial (Totals.Totals X)) X
RF {X} = record { 
  fun   = F; 
  frest = λ {_ _ f} → tot f }
  where open Totals X
        open Tot

RFFaithful : ∀{X} → Faithful (F {X})
RFFaithful {X} = TotEq
  where open Totals X
        open Tot


-- split restriction category

record SplitRestCat : Set where
  field rcat   : RestCat
  open RestCat rcat
  open Cat cat
  open Lemmata rcat
  open Idems cat
  field rsplit : ∀{E A}(f : Hom E A) → 
                 Split (record { E = E; e = rest f; law = lemii})


-- In a split restriction category X the class
-- of monics that split restriction idempotents forms
-- a stable system of monics in Total(X)

module MonicClass (X : SplitRestCat) where

  open SplitRestCat X
  open RestCat rcat
  open Cat cat
  open Lemmata rcat
  open Idems cat

  record SRestIde {B E} (s : Hom B E) : Set where
    field As    : Obj
          fs    : Hom E As
          rs    : Hom E B
          law1s : comp s rs ≅ rest fs
          law2s : comp rs s ≅ iden {B}

  open Monos cat
  open Isos cat

  SRIde→Split : ∀{B E}{s : Hom B E} → (sride : SRestIde s) → 
                let open SRestIde sride
                in Split (record { E = E; e = rest fs; law = lemii })
  SRIde→Split {B}{E}{s} sride = 
    let open SRestIde sride
    in record { 
      B = B; 
      s = s; 
      r = rs; 
      law1 = law1s; 
      law2 = law2s }

  SRIdeProp : ∀{B E}{s : Hom B E} → (sride : SRestIde s) →
    let open SRestIde sride
    in comp s rs ≅ rest rs
  SRIdeProp {_}{_}{s} sride = 
    let open SRestIde sride
    in 
    proof
    comp s rs
    ≅⟨ law1s ⟩ 
    rest fs
    ≅⟨ sym lemi ⟩
    rest (rest fs)
    ≅⟨ cong rest (sym law1s) ⟩
    rest (comp s rs)
    ≅⟨ lemiv ⟩
    rest (comp (rest s) rs)
    ≅⟨ cong (λ y → rest (comp y rs)) (lemiii (smon {_} {SRIde→Split sride})) ⟩
    rest (comp iden rs)
    ≅⟨ cong rest idl ⟩
    rest rs
    ∎

  MXmon : ∀{B E}{s : Hom B E} → SRestIde s → Mono s
  MXmon sride = smon {_} {SRIde→Split sride} 

  MXiso : ∀{B E}{s : Hom B E} → Iso s → SRestIde s
  MXiso {_}{E}{s} (g , p , q) = record { 
    As = E; 
    fs = iden; 
    rs = g; 
    law1s = 
      proof
      comp s g
      ≅⟨ p ⟩
      iden
      ≅⟨ sym (lemiii idmono) ⟩
      rest iden
      ∎; 
    law2s = q }

  MXcomp : ∀{B E E'}{s : Hom B E}{s' : Hom E E'} → SRestIde s → 
           SRestIde s' → SRestIde (comp s' s)
  MXcomp {B}{E}{E'}{s}{s'} sride sride' =
    let open SRestIde sride
        open SRestIde sride' renaming (As to As';
                                       fs to fs';
                                       rs to rs';
                                       law1s to law1s';
                                       law2s to law2s')
     in record { 
       As = B; 
       fs = comp (comp rs rs') (rest rs'); 
       rs = comp rs rs'; 
       law1s = 
         proof
         comp (comp s' s) (comp rs rs')
         ≅⟨ ass ⟩
         comp s' (comp s (comp rs rs'))
         ≅⟨ cong (comp s') (sym ass) ⟩
         comp s' (comp (comp s rs) rs')
         ≅⟨ cong (λ y → comp s' (comp y rs')) (SRIdeProp sride) ⟩
         comp s' (comp (rest rs) rs')
         ≅⟨ cong (comp s') R4 ⟩
         comp s' (comp rs' (rest (comp rs rs')))
         ≅⟨ sym ass ⟩
         comp (comp s' rs') (rest (comp rs rs'))
         ≅⟨ cong (λ y → comp y (rest (comp rs rs'))) (SRIdeProp sride') ⟩
         comp (rest rs') (rest (comp rs rs'))
         ≅⟨ R2 ⟩
         comp (rest (comp rs rs')) (rest rs')
         ≅⟨ R3 ⟩
         rest (comp (comp rs rs') (rest rs'))
         ∎; 
       law2s = 
         proof
         comp (comp rs rs') (comp s' s)
         ≅⟨ ass ⟩
         comp rs (comp rs' (comp s' s))
         ≅⟨ cong (comp rs) (sym ass) ⟩
         comp rs (comp (comp rs' s') s)
         ≅⟨ cong (λ y → comp rs (comp y s)) law2s' ⟩
         comp rs (comp iden s)
         ≅⟨ cong (comp rs) idl ⟩
         comp rs s
         ≅⟨ law2s ⟩
         iden
         ∎ } 

  open import Pullbacks cat

  MXpul : ∀{A B E}(f : Hom A E){s : Hom B E} → SRestIde s → 
          Σ (Pullback f s) λ p → 
          let open Pullback p
              open Square sq
           in SRestIde h 
  MXpul {A}{B}{E} f {s} sride = {!!}
             
  open import Stable

  MX : StableSys cat
  MX = record { 
    ∈ = SRestIde; 
    mon = MXmon; 
    iso = MXiso; 
    com = MXcomp; 
    pul = MXpul }



