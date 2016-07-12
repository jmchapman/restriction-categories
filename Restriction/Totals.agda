
open import Restriction.Cat

module Restriction.Totals {i j}(X : RestCat {i}{j}) where

open import Utilities
open import Categories
open RestCat X
open Lemmata X
open Cat cat
open import Categories.Monos cat
open import Categories.Isos 

record Tot (A B : Obj) : Set j where
  constructor tot
  field hom     : Hom A B 
        totProp : rest hom ≅ iden {A}

open Tot

totEq : ∀{A B}{f g : Hom A B}
        {p : rest f ≅ iden}{q : rest g ≅ iden} → 
        f ≅ g → tot f p ≅ tot g q 
totEq refl = cong (tot _) (proof-irr _ _)

idTot : ∀{A} → Tot A A
idTot = tot iden (lemiii idMono)

compTotProp : ∀{A B C}{g : Tot B C}{f : Tot A B} → 
              rest (comp (hom g) (hom f)) ≅ iden
compTotProp {g = g}{f} = 
  proof
  rest (comp (hom g) (hom f)) 
  ≅⟨ lemiv ⟩ 
  rest (comp (rest (hom g)) (hom f))
  ≅⟨ cong (λ h → rest (comp h (hom f))) (totProp g) ⟩ 
  rest (comp iden (hom f))
  ≅⟨ cong rest idl ⟩ 
  rest (hom f)
  ≅⟨ totProp f ⟩ 
  iden
  ∎
  
compTot : ∀{A B C}(g : Tot B C)(f : Tot A B) → Tot A C
compTot g f = tot (comp (hom g) (hom f)) (compTotProp {g = g}{f})

Total : Cat
Total = record {
  Obj  = Obj; 
  Hom  = Tot;
  iden = idTot;
  comp = compTot;
  idl  = totEq idl;
  idr  = totEq idr;
  ass  = totEq ass}


isoTot : ∀{A B}{f : Hom A B}{p} → Iso cat f → Iso Total (tot f p)
isoTot (iso g q r) = 
  iso (tot g (lemiii (isoIsMono cat (iso _ r q)))) (totEq q) (totEq r)

totEqHom : ∀{A B}{f g : Tot A B} → f ≅ g → hom f ≅ hom g
totEqHom p = cong hom p

-- .monoTot : ∀{A B}(f : Tot A B) → Mono cat (hom f) → Mono Total f
-- monoTot f p {_}{_}{_} q = {!!} --totEq (p (cong hom q))

{-
.MonoTot : ∀{A B}(f : Tot A B) → Mono cat (hom f) → Mono Total f
MonoTot f p q = TotEq (p (cong hom q))

IsoTot : ∀{A B}(f : Tot A B) → Iso cat (hom f) → Iso Total f
IsoTot f fiso = 
  let open Iso cat fiso renaming (inv to g; rinv to p; linv to q) 
      open Tot f renaming (hom to fhom)
      gt = record { 
        hom = g; 
        tot = isoIsMono cat (iso fhom q p) 
                       (proof
                        comp g (rest g)
                        ≅⟨ R1 ⟩
                        g
                        ≅⟨ sym idr ⟩
                        comp g iden
                        ∎) }

  in iso gt (TotEq p) (TotEq q)

TotEqHom : ∀{A B}{f g : Tot A B} → f ≅ g → hom f ≅ hom g
TotEqHom p = cong hom p
-}

