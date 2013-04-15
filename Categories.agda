{-# OPTIONS --type-in-type #-}
module Categories where

open import Relation.Binary.HeterogeneousEquality
open import Equality
open ≅-Reasoning renaming (begin_ to proof_)
open import Data.Product
open import Function

record Cat : Set where
  field Obj  : Set
        Hom  : Obj → Obj → Set
        iden : ∀{X} → Hom X X
        comp : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → comp iden f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → comp f iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
               comp (comp f g) h ≅ comp f (comp g h)

module Monos (X : Cat) where
  open Cat X

  Mono : ∀{A B} → Hom A B → Set
  Mono f = ∀{C}{g h : Hom C _} → comp f g ≅ comp f h → g ≅ h

  idmono : ∀{A} → Mono (iden {A})
  idmono {_}{_}{g}{h} p = 
    proof
    g 
    ≅⟨ sym idl ⟩ 
    comp iden g 
    ≅⟨ p ⟩ 
    comp iden h 
    ≅⟨ idl ⟩ 
    h 
    ∎

  compmonos : ∀{A B C}(f : Hom A B)(g : Hom B C) → Mono f → Mono g → 
              Mono (comp g f)
  compmonos f g p q {D}{h1}{h2} r = p $ q $
    proof 
    comp g (comp f h1)
    ≅⟨ sym ass ⟩ 
    comp (comp g f) h1 
    ≅⟨ r ⟩ 
    comp (comp g f) h2 
    ≅⟨ ass ⟩ 
    comp g (comp f h2) 
    ∎


module Epis (X : Cat) where
  open Cat X

  Epi : ∀{A B} → Hom A B → Set
  Epi f = ∀{C}{g h : Hom _ C} → comp g f ≅ comp h f → g ≅ h


module Isos (X : Cat) where
  open Cat X

  Iso : ∀{A B} → Hom A B → Set
  Iso {A}{B} f = Σ (Hom B A) (λ g → comp f g ≅ iden {B} × comp g f ≅ iden {A})

  idiso : ∀{A} → Iso (iden {A})
  idiso = iden , idl , idl

  invuniq : ∀{A B}(f : Hom A B)(p q : Iso f) → proj₁ p ≅ proj₁ q
  invuniq f (g , p , p') (g' , q , q') = 
    proof 
    g 
    ≅⟨ sym idr ⟩ 
    comp g iden
    ≅⟨ cong (comp g) (sym q) ⟩ 
    comp g (comp f g')
    ≅⟨ sym ass ⟩ 
    comp (comp g f) g'
    ≅⟨ cong (λ h → comp h g') p' ⟩     
    comp iden g'
    ≅⟨ idl ⟩     
    g'
    ∎

  open Monos X
  iso→mono : ∀{A B}{f : Hom A B} → Iso f → Mono f
  iso→mono {_}{_}{f} (f' , p , p') {_}{g}{h} q = 
    proof 
    g 
    ≅⟨ sym idl ⟩ 
    comp iden g 
    ≅⟨ cong (λ h → comp h g) (sym p') ⟩ 
    comp (comp f' f) g 
    ≅⟨ ass ⟩ 
    comp f' (comp f g) 
    ≅⟨ cong (comp f') q ⟩ 
    comp f' (comp f h) 
    ≅⟨ sym ass ⟩ 
    comp (comp f' f) h 
    ≅⟨ cong (λ g → comp g h) p' ⟩ 
    comp iden h 
    ≅⟨ idl ⟩ 
    h 
    ∎

  compisos : ∀{A B C}{f : Hom A B}{g : Hom B C} → Iso f → Iso g → 
             Iso (comp g f)
  compisos {_}{_}{_} {f} {g} (f' , p , p') (g' , q , q') = 
    (comp f' g') , 
    (proof 
     comp (comp g f) (comp f' g') 
     ≅⟨ ass ⟩ 
     comp g (comp f (comp f' g')) 
     ≅⟨ cong (comp g) (sym ass) ⟩ 
     comp g (comp (comp f f') g') 
     ≅⟨ cong (λ h → comp g (comp h g')) p ⟩ 
     comp g (comp iden g') 
     ≅⟨ cong (comp g) idl ⟩ 
     comp g g' 
     ≅⟨ q ⟩ 
     iden 
     ∎) , 
    (proof 
     comp (comp f' g') (comp g f) 
     ≅⟨ ass ⟩ 
     comp f' (comp g' (comp g f)) 
     ≅⟨ cong (comp f') (sym ass) ⟩ 
     comp f' (comp (comp g' g) f) 
     ≅⟨ cong (λ h → comp f' (comp h f)) q' ⟩ 
     comp f' (comp iden f) 
     ≅⟨ cong (comp f') idl ⟩ 
     comp f' f 
     ≅⟨ p' ⟩ 
     iden 
     ∎)

module Idems (X : Cat) where
  open Cat X

  record Idem : Set where
    field E : Obj
          e : Hom E E
          law : comp e e ≅ e

  record Split (ide : Idem) : Set where
    open Idem ide
    field B : Obj 
          s : Hom B E
          r : Hom E B
          law1 : comp s r ≅ e
          law2 : comp r s ≅ iden {B}

  open Epis X
  open Monos X

  repi : ∀{e : Idem}{sp : Split e} → 
         let open Split sp
         in
         Epi r
  repi {_}{sp}{_}{g}{h} p = 
    let open Split sp
    in
    proof 
    g 
    ≅⟨ sym idr ⟩ 
    comp g iden 
    ≅⟨ cong (comp g) (sym law2) ⟩ 
    comp g (comp r s) 
    ≅⟨ sym ass ⟩ 
    comp (comp g r) s 
    ≅⟨ cong (λ y → comp y s) p ⟩ 
    comp (comp h r) s 
    ≅⟨ ass ⟩ 
    comp h (comp r s) 
    ≅⟨ cong (comp h) law2 ⟩ 
    comp h iden 
    ≅⟨ idr ⟩ 
    h 
    ∎

  smon : ∀{e : Idem}{sp : Split e} → 
         let open Split sp
         in
         Mono s
  smon {_}{sp}{_}{g}{h} p = 
    let open Split sp
    in
    proof
    g
    ≅⟨ sym idl ⟩
    comp iden g
    ≅⟨ cong (λ y → comp y g) (sym law2) ⟩
    comp (comp r s) g
    ≅⟨ ass ⟩
    comp r (comp s g)
    ≅⟨ cong (comp r) p ⟩
    comp r (comp s h)
    ≅⟨ sym ass ⟩
    comp (comp r s) h
    ≅⟨ cong (λ y → comp y h) law2 ⟩
    comp iden h
    ≅⟨ idl ⟩
    h
    ∎

  lemma : ∀(e : Idem)(sp sp' : Split e) → 
          let open Isos X
              open Split sp
              open Split sp' renaming (B to B'; s to s'; r to r')
          in
          Σ (Hom B B') λ α → Iso α × comp α r ≅ r' × comp s' α ≅ s
  lemma ide sp sp' =  
    let open Isos X
        open Idem ide
        open Split sp
        open Split sp' renaming (B to B'; 
                                 s to s'; 
                                 r to r';
                                 law1 to law1';
                                 law2 to law2')
    in comp r' s 
       , 
       (comp r s' 
        , 
        (proof 
         comp (comp r' s) (comp r s') 
         ≅⟨ ass ⟩ 
         comp r' (comp s (comp r s'))
         ≅⟨ cong (comp r') (sym ass) ⟩ 
         comp r' (comp (comp s r) s')
         ≅⟨ cong (λ f → comp r' (comp f s')) law1 ⟩ 
         comp r' (comp e s')
         ≅⟨ cong (λ f → comp r' (comp f s')) (sym law1') ⟩ 
         comp r' (comp (comp s' r') s')
         ≅⟨ cong (comp r') ass ⟩
         comp r' (comp s' (comp r' s'))
         ≅⟨ cong (comp r' ∘ comp s') law2' ⟩
         comp r' (comp s' iden)
         ≅⟨ sym ass ⟩
         comp (comp r' s') iden
         ≅⟨ idr ⟩
         comp r' s'
         ≅⟨ law2' ⟩
         iden 
         ∎) 
        , 
        (proof 
         comp (comp r s') (comp r' s) 
         ≅⟨ ass ⟩
         comp r (comp s' (comp r' s))
         ≅⟨ cong (comp r) (sym ass) ⟩ 
         comp r (comp (comp s' r') s)
         ≅⟨ cong (λ f → comp r (comp f s)) law1' ⟩ 
         comp r (comp e s)
         ≅⟨ cong (λ f → comp r (comp f s)) (sym law1) ⟩ 
         comp r (comp (comp s r) s)
         ≅⟨ cong (comp r) ass ⟩
         comp r (comp s (comp r s))
         ≅⟨ cong (comp r ∘ comp s) law2 ⟩
         comp r (comp s iden)
         ≅⟨ sym ass ⟩
         comp (comp r s) iden
         ≅⟨ idr ⟩
         comp r s
         ≅⟨ law2 ⟩
         iden 
         ∎))
       , 
       (proof 
        comp (comp r' s) r 
        ≅⟨ ass ⟩ 
        comp r' (comp s r)
        ≅⟨ cong (comp r') law1 ⟩ 
        comp r' e
        ≅⟨ cong (comp r') (sym law1') ⟩ 
        comp r' (comp s' r')
        ≅⟨ sym ass ⟩ 
        comp (comp r' s') r'
        ≅⟨ cong (λ f → comp f r') law2' ⟩ 
        comp iden r'
        ≅⟨ idl ⟩ 
        r'
        ∎) 
       , 
       (proof 
        comp s' (comp r' s) 
        ≅⟨ sym ass ⟩ 
        comp (comp s' r') s
        ≅⟨ cong (λ f → comp f s) law1' ⟩ 
        comp e s
        ≅⟨ cong (λ f → comp f s) (sym law1) ⟩ 
        comp (comp s r) s
        ≅⟨ ass ⟩ 
        comp s (comp r s)
        ≅⟨ cong (comp s) law2 ⟩ 
        comp s iden
        ≅⟨ idr ⟩ 
        s
        ∎)


{-

-- here Idem is a type that takes the object as an argument

module Idems (X : Cat) where
  open Cat X

  record Idem X : Set where
    field e : Hom X X
          law : comp e e ≅ e

  record Split {A}(ide : Idem A) : Set where
    open Idem ide
    field B : Obj 
          s : Hom B A
          r : Hom A B
          law1 : comp s r ≅ e
          law2 : comp r s ≅ iden {B}

  open Epis X
  open Monos X

  repi : ∀{A}{e : Idem A}{sp : Split e} → 
         let open Split sp
         in
         Epi r
  repi {_}{_}{sp}{_}{g}{h} p = 
    let open Split sp
    in
    proof 
    g 
    ≅⟨ sym idr ⟩ 
    comp g iden 
    ≅⟨ cong (comp g) (sym law2) ⟩ 
    comp g (comp r s) 
    ≅⟨ sym ass ⟩ 
    comp (comp g r) s 
    ≅⟨ cong (λ y → comp y s) p ⟩ 
    comp (comp h r) s 
    ≅⟨ ass ⟩ 
    comp h (comp r s) 
    ≅⟨ cong (comp h) law2 ⟩ 
    comp h iden 
    ≅⟨ idr ⟩ 
    h 
    ∎

  smon : ∀{A}{e : Idem A}{sp : Split e} → 
         let open Split sp
         in
         Mono s
  smon {_}{_}{sp}{_}{g}{h} p = 
    let open Split sp
    in
    proof
    g
    ≅⟨ sym idl ⟩
    comp iden g
    ≅⟨ cong (λ y → comp y g) (sym law2) ⟩
    comp (comp r s) g
    ≅⟨ ass ⟩
    comp r (comp s g)
    ≅⟨ cong (comp r) p ⟩
    comp r (comp s h)
    ≅⟨ sym ass ⟩
    comp (comp r s) h
    ≅⟨ cong (λ y → comp y h) law2 ⟩
    comp iden h
    ≅⟨ idl ⟩
    h
    ∎

  lemma : ∀{A}(e : Idem A)(sp sp' : Split e) → 
          let open Isos X
              open Split sp
              open Split sp' renaming (B to B'; s to s'; r to r')
          in
          Σ (Hom B B') λ α → Iso α × comp α r ≅ r' × comp s' α ≅ s
  lemma ide sp sp' =  
    let open Isos X
        open Idem ide
        open Split sp
        open Split sp' renaming (B to B'; 
                                 s to s'; 
                                 r to r';
                                 law1 to law1';
                                 law2 to law2')
    in comp r' s 
       , 
       (comp r s' 
        , 
        (proof 
         comp (comp r' s) (comp r s') 
         ≅⟨ ass ⟩ 
         comp r' (comp s (comp r s'))
         ≅⟨ cong (comp r') (sym ass) ⟩ 
         comp r' (comp (comp s r) s')
         ≅⟨ cong (λ f → comp r' (comp f s')) law1 ⟩ 
         comp r' (comp e s')
         ≅⟨ cong (λ f → comp r' (comp f s')) (sym law1') ⟩ 
         comp r' (comp (comp s' r') s')
         ≅⟨ cong (comp r') ass ⟩
         comp r' (comp s' (comp r' s'))
         ≅⟨ cong (comp r' ∘ comp s') law2' ⟩
         comp r' (comp s' iden)
         ≅⟨ sym ass ⟩
         comp (comp r' s') iden
         ≅⟨ idr ⟩
         comp r' s'
         ≅⟨ law2' ⟩
         iden 
         ∎) 
        , 
        (proof 
         comp (comp r s') (comp r' s) 
         ≅⟨ ass ⟩
         comp r (comp s' (comp r' s))
         ≅⟨ cong (comp r) (sym ass) ⟩ 
         comp r (comp (comp s' r') s)
         ≅⟨ cong (λ f → comp r (comp f s)) law1' ⟩ 
         comp r (comp e s)
         ≅⟨ cong (λ f → comp r (comp f s)) (sym law1) ⟩ 
         comp r (comp (comp s r) s)
         ≅⟨ cong (comp r) ass ⟩
         comp r (comp s (comp r s))
         ≅⟨ cong (comp r ∘ comp s) law2 ⟩
         comp r (comp s iden)
         ≅⟨ sym ass ⟩
         comp (comp r s) iden
         ≅⟨ idr ⟩
         comp r s
         ≅⟨ law2 ⟩
         iden 
         ∎))
       , 
       (proof 
        comp (comp r' s) r 
        ≅⟨ ass ⟩ 
        comp r' (comp s r)
        ≅⟨ cong (comp r') law1 ⟩ 
        comp r' e
        ≅⟨ cong (comp r') (sym law1') ⟩ 
        comp r' (comp s' r')
        ≅⟨ sym ass ⟩ 
        comp (comp r' s') r'
        ≅⟨ cong (λ f → comp f r') law2' ⟩ 
        comp iden r'
        ≅⟨ idl ⟩ 
        r'
        ∎) 
       , 
       (proof 
        comp s' (comp r' s) 
        ≅⟨ sym ass ⟩ 
        comp (comp s' r') s
        ≅⟨ cong (λ f → comp f s) law1' ⟩ 
        comp e s
        ≅⟨ cong (λ f → comp f s) (sym law1) ⟩ 
        comp (comp s r) s
        ≅⟨ ass ⟩ 
        comp s (comp r s)
        ≅⟨ cong (comp s) law2 ⟩ 
        comp s iden
        ≅⟨ idr ⟩ 
        s
        ∎)
-}  

_Op : Cat → Cat
C Op = record {
  Obj  = Obj; 
  Hom  = λ X Y → Hom Y X;
  iden = iden;
  comp = λ f g → comp g f; 
  idl  = idr;
  idr  = idl;
  ass  = sym ass}
  where open Cat C
