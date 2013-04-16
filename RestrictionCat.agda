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
               comp (rest g) f ≅ comp f (rest (comp g f))


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
  open Monos

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

  Total : Cat
  Total = record {
    Obj  = Obj; 
    Hom  = Tot;
    iden = record { hom = iden; tot = lemiii (idmono cat) };
    comp = comptot;
    idl  = TotEq idl;
    idr  = TotEq idr;
    ass  = TotEq ass}

  MonoTot : ∀{A B}(f : Tot A B) → Mono cat (hom f) → Mono Total f
  MonoTot f p {C}{g}{h} q = TotEq (p (cong hom q))

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
  open Totals rcat
  open Tot

  record SRestIde {B E} (s : Tot B E) : Set where
    field As    : Obj
          fs    : Hom E As
          rs    : Hom E B
          law1s : comp (hom s) rs ≅ rest fs
          law2s : comp rs (hom s) ≅ iden {B}

  open Monos
  open Isos Total
  open Sections cat

{-
  SRIde→Split : ∀{B E}{s : Tot B E} → (sride : SRestIde s) → 
                let open SRestIde sride
                in Split (record { E = E; e = rest fs; law = lemii })
  SRIde→Split {B}{E}{s} sride = 
    let open SRestIde sride
    in record { 
      B = B; 
      s = hom s; 
      r = rs; 
      law1 = law1s; 
      law2 = law2s }


  MXmon : ∀{B E}{s : Tot B E} → SRestIde s → Mono Total s
  MXmon {_}{_}{s} sride {_}{g}{h} q = TotEq (smon (hom s) (SRestIde.rs sride , SRestIde.law2s sride) (cong hom q))

  MXiso : ∀{B E}{s : Tot B E} → Iso s → SRestIde s
  MXiso {_}{E}{s} (g , p , q) = record { 
    As = E; 
    fs = iden; 
    rs = hom g; 
    law1s =       
      proof
      comp (hom s) (hom g)
      ≅⟨ cong hom p ⟩
      iden
      ≅⟨ sym (lemiii (idmono cat)) ⟩
      rest iden
      ∎; 
    law2s = cong hom q }
 
  SRIdeProp : ∀{B E}{s : Tot B E} → (sride : SRestIde s) →
    let open SRestIde sride
    in comp (hom s) rs ≅ rest rs
  SRIdeProp {_}{_}{s} sride = 
    let open SRestIde sride
    in 
    proof
    comp (hom s) rs
    ≅⟨ law1s ⟩ 
    rest fs
    ≅⟨ sym lemi ⟩
    rest (rest fs)
    ≅⟨ cong rest (sym law1s) ⟩
    rest (comp (hom s) rs)
    ≅⟨ lemiv ⟩
    rest (comp (rest (hom s)) rs)
    ≅⟨ cong (λ y → rest (comp y rs)) (lemiii (smon (hom s) (SRestIde.rs sride , SRestIde.law2s sride))) ⟩ 
    rest (comp iden rs)
    ≅⟨ cong rest idl ⟩
    rest rs
    ∎

  MXcomp : ∀{B E E'}{s : Tot B E}{s' : Tot E E'} → SRestIde s → 
           SRestIde s' → SRestIde (comptot s' s)
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
         comp (comp (hom s') (hom s)) (comp rs rs')
         ≅⟨ ass ⟩
         comp (hom s') (comp (hom s) (comp rs rs'))
         ≅⟨ cong (comp (hom s')) (sym ass) ⟩
         comp (hom s') (comp (comp (hom s) rs) rs')
         ≅⟨ cong (λ y → comp (hom s') (comp y rs')) (SRIdeProp sride) ⟩
         comp (hom s') (comp (rest rs) rs')
         ≅⟨ cong (comp (hom s')) R4 ⟩
         comp (hom s') (comp rs' (rest (comp rs rs')))
         ≅⟨ sym ass ⟩
         comp (comp (hom s') rs') (rest (comp rs rs'))
         ≅⟨ cong (λ y → comp y (rest (comp rs rs'))) (SRIdeProp sride') ⟩
         comp (rest rs') (rest (comp rs rs'))
         ≅⟨ R2 ⟩
         comp (rest (comp rs rs')) (rest rs')
         ≅⟨ R3 ⟩
         rest (comp (comp rs rs') (rest rs'))
         ∎ ;
       law2s = 
         proof
         comp (comp rs rs') (comp (hom s') (hom s))
         ≅⟨ ass ⟩
         comp rs (comp rs' (comp (hom s') (hom s)))
         ≅⟨ cong (comp rs) (sym ass) ⟩
         comp rs (comp (comp rs' (hom s')) (hom s))
         ≅⟨ cong (λ y → comp rs (comp y (hom s))) law2s' ⟩
         comp rs (comp iden (hom s))
         ≅⟨ cong (comp rs) idl ⟩
         comp rs (hom s)
         ≅⟨ law2s ⟩
         iden
         ∎}

-}

  open import Pullbacks Total

  MXpul : ∀{A B C}(ft : Tot C B){mt : Tot A B} → SRestIde mt → 
          Σ (Pullback ft mt) λ p → 
          let open Pullback p
              open Square sq renaming (h to mt')
          in SRestIde mt'
  MXpul {A}{B}{C} ft {mt} sride = 
    let open SRestIde sride renaming (fs to u; 
                                      rs to r; 
                                      law1s to law1e; 
                                      law2s to law2e)
        open Tot mt renaming (hom to m; tot to mp)
        open Tot ft renaming (hom to f; tot to fp)

        e : Hom B B
        e = rest u

        e' : Hom C C
        e' = rest (comp e f)

        open Split (rsplit (comp e f)) renaming (B to D; 
                                                 s to m'; 
                                                 r to r';
                                                 law1 to law1e';
                                                 law2 to law2e')

        f' : Hom D A
        f' = comp r (comp f m')
  
        mp' = lemiii (smon m' ((r' , law2e')))

        sq : Square ft mt
        sq = record { 
          W = D; 
          h = record { 
            hom = m'; 
            tot = mp'};
          k = record { 
            hom = f';
            tot = {!!}};
{-
              proof
              rest (comp r (comp f m'))
              ≅⟨ cong rest (sym idl) ⟩
              rest (comp iden (comp r (comp f m')))
              ≅⟨ cong (λ y → rest (comp y (comp r (comp f m')))) (sym mp) ⟩
              rest (comp (rest m) (comp r (comp f m')))
              ≅⟨ sym lemiv ⟩
              rest (comp m (comp r (comp f m')))
              ≅⟨ cong rest (sym ass) ⟩
              rest (comp (comp m r) (comp f m'))
              ≅⟨ cong (λ y → rest (comp y (comp f m'))) law1e ⟩
              rest (comp e (comp f m'))
              ≅⟨ cong rest (sym ass) ⟩
              rest (comp (comp e f) m')
              ≅⟨ lemiv ⟩
              rest (comp e' m')
              ≅⟨ cong (λ y → rest (comp y m')) (sym law1e') ⟩
              rest (comp (comp m' r') m')
              ≅⟨ cong rest ass ⟩
              rest (comp m' (comp r' m'))
              ≅⟨ cong (λ y → rest (comp m' y)) law2e' ⟩
              rest (comp m' iden)
              ≅⟨ cong rest idr ⟩
              rest m'
              ≅⟨ mp' ⟩
              iden
              ∎ ; 
-}
          scom = {!!}}
{-
TotEq (
            proof 
            comp f m' 
            ≅⟨ sym idr ⟩ 
            comp (comp f m') iden
            ≅⟨ cong (comp (comp f m')) (sym law2e') ⟩ 
            comp (comp f m') (comp r' m')
            ≅⟨ ass ⟩ 
            comp f (comp m' (comp r' m'))
            ≅⟨ cong (comp f) (sym ass) ⟩ 
            comp f (comp (comp m' r') m')
            ≅⟨ cong (λ y → comp f (comp y m')) law1e' ⟩ 
            comp f (comp (rest (comp e f)) m')
            ≅⟨ sym ass ⟩ 
            comp (comp f (rest (comp e f))) m'
            ≅⟨ cong (λ y → comp y m') (sym R4) ⟩ 
            comp (comp (rest e) f) m'
            ≅⟨ cong (λ y → comp (comp y f) m') lemi ⟩ 
            comp (comp e f) m'
            ≅⟨ cong (λ y → comp (comp y f) m') (sym law1e) ⟩ 
            comp (comp (comp m r) f) m'
            ≅⟨ ass ⟩ 
            comp (comp m r) (comp f m')
            ≅⟨ ass ⟩ 
            comp m f' 
            ∎) 
            }
-}
    in (record { 
          sq = sq; 
          prop = λ sq' → 
            let open Square sq' renaming (W to D';
                                          h to xt;
                                          k to yt;
                                          scom to scom')

                open Tot xt renaming (hom to x; tot to xp)
                open Tot yt renaming (hom to y; tot to yp)

                α : Hom D' D
                α = comp r' x

                αp2 : comp f' α ≅ y
                αp2 = smon m (r , law2e) 
                  (proof
                   comp m (comp (comp r (comp f m')) (comp r' x))
                   ≅⟨ cong (comp m) ass ⟩
                   comp m (comp r (comp (comp f m') (comp r' x)))
                   ≅⟨ sym ass ⟩
                   comp (comp m r) (comp (comp f m') (comp r' x))
                   ≅⟨ cong (λ y → comp y (comp (comp f m') (comp r' x))) law1e ⟩
                   comp e (comp (comp f m') (comp r' x))
                   ≅⟨ cong (comp e) ass ⟩
                   comp e (comp f (comp m' (comp r' x)))
                   ≅⟨ cong (comp e ∘ comp f) (sym ass) ⟩
                   comp e (comp f (comp (comp m' r') x))
                   ≅⟨ cong (λ y → comp e (comp f (comp y x))) law1e' ⟩
                   comp e (comp f (comp (rest (comp e f)) x))
                   ≅⟨ sym ass ⟩
                   comp (comp e f) (comp (rest (comp e f)) x)
                   ≅⟨ sym ass ⟩
                   comp (comp (comp e f) (rest (comp e f))) x
                   ≅⟨ cong (λ y → comp y x) R1 ⟩
                   comp (comp e f) x
                   ≅⟨ ass ⟩
                   comp e (comp f x)
                   ≅⟨ cong (comp e) (cong hom scom') ⟩
                   comp e (comp m y)
                   ≅⟨ cong (λ z → comp z (comp m y)) (sym law1e) ⟩
                   comp (comp m r) (comp m y)
                   ≅⟨ ass ⟩
                   comp m (comp r (comp m y))
                   ≅⟨ cong (comp m) (sym ass) ⟩
                   comp m (comp (comp r m) y)
                   ≅⟨ cong (λ z → comp m (comp z y)) law2e  ⟩
                   comp m (comp iden y)
                   ≅⟨ cong (comp m) idl ⟩
                   comp m y
                   ∎)

                αp : comp m' α ≅ x
                αp = 
                  proof
                  comp m' α
                  ≅⟨ sym ass ⟩
                  comp (comp m' r') x
                  ≅⟨ cong (λ z → comp z x) law1e' ⟩
                  comp (rest (comp e f)) x
                  ≅⟨ R4 ⟩
                  comp x (rest (comp (comp e f) x)) 
                  ≅⟨ cong (comp x ∘ rest) ass ⟩
                  comp x (rest (comp e (comp f x))) 
                  ≅⟨ cong (comp x ∘ rest ∘ comp e) (cong hom scom') ⟩
                  comp x (rest (comp e (comp m y))) 
                  ≅⟨ cong (λ z → comp x (rest (comp z (comp m y)))) (sym law1e) ⟩
                  comp x (rest (comp (comp m r) (comp m y))) 
                  ≅⟨ cong (comp x ∘ rest) ass ⟩
                  comp x (rest (comp m (comp r (comp m y)))) 
                  ≅⟨ cong (comp x ∘ rest ∘ comp m) (sym ass) ⟩
                  comp x (rest (comp m (comp (comp r m) y))) 
                  ≅⟨ cong (λ z → comp x (rest (comp m (comp z y)))) law2e  ⟩
                  comp x (rest (comp m (comp iden y))) 
                  ≅⟨ cong (comp x ∘ rest ∘ comp m) idl ⟩
                  comp x (rest (comp m y)) 
                  ≅⟨ cong (comp x) lemiv ⟩
                  comp x (rest (comp (rest m) y)) 
                  ≅⟨ cong (λ z → comp x (rest (comp z y))) mp ⟩
                  comp x (rest (comp iden y)) 
                  ≅⟨ cong (comp x ∘ rest) idl ⟩
                  comp x (rest y) 
                  ≅⟨ cong (comp x) yp ⟩
                  comp x iden 
                  ≅⟨ idr ⟩
                  x
                  ∎

            in record { 
                 mor = record { 
                   hom = α; 
                   tot = {!!}};
{-
                     proof
                     rest (comp r' x)
                     ≅⟨ cong rest (sym idl) ⟩
                     rest (comp iden (comp r' x))
                     ≅⟨ cong (λ y → rest (comp y (comp r' x))) (sym mp') ⟩
                     rest (comp (rest m') (comp r' x))
                     ≅⟨ sym lemiv ⟩
                     rest (comp m' (comp r' x))
                     ≅⟨ cong rest αp ⟩
                     rest x
                     ≅⟨ xp ⟩
                     iden
                     ∎ }; 
-}
                 prop1 = TotEq αp; 
                 prop2 = TotEq αp2} ,
               (λ umap' → 
                let open PMap umap' renaming (mor to ut')
                    open Tot ut' renaming (hom to u')
                in TotEq (smon m' (r' , law2e') 
                   (proof
                    comp m' α
                    ≅⟨ αp ⟩
                    x
                    ≅⟨ cong hom (sym prop1) ⟩
                    comp m' u'
                    ∎))) }) , 
               record { As = B; fs = comp e f; rs = r'; law1s = law1e'; law2s = law2e' }

{-
  open import Stable

  M : StableSys Total
  M = record { 
    ∈ = SRestIde; 
    mon = MXmon;
    iso = MXiso; 
    com = MXcomp; 
    pul = MXpul }
-}




    