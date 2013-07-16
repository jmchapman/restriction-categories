module SplitRestCats where

open import Categories
open import RestrictionCat
open import Relation.Binary.HeterogeneousEquality
open import Utilities
open ≅-Reasoning renaming (begin_ to proof_)
open import Function
open import Data.Product
open import Level

 -- split restriction category

import Categories.Idems

record SplitRestCat {a b} : Set (suc (a ⊔ b)) where
  field rcat   : RestCat {a}{b}
  open RestCat rcat
  open Cat cat
  open Lemmata rcat
  open Categories.Idems cat
  field rsplit : ∀{E A}(f : Hom E A) → 
                 Split (record { E = E; e = rest f; law = lemii})

open import Splits


-- SplitCat is a restriction category (if X is)

.restprop : ∀{a b}{X : RestCat {a}{b}} → 
           let open RestCat X
               open Cat cat
               open Categories.Idems cat
           in {ide ide' : Idem}(f : SplitMap cat ide ide') →
           let open SplitMap cat f
               open Idem ide
           in comp (rest imap) e ≅ comp e (rest imap)
restprop {_}{_}{X}{ide}{_} f = 
  let open RestCat X
      open Cat cat
      open Categories.Idems cat
      open SplitMap cat f
      open Idem ide
  in 
    proof
    comp (rest imap) e
    ≅⟨ R4 ⟩
    comp e (rest (comp imap e))
    ≅⟨ cong (comp e ∘ rest) (splitprop cat f) ⟩
    comp e (rest imap)
    ∎           

restsplitmap : ∀{a b}{X : RestCat {a}{b}} → 
               let open RestCat X
                   open Cat cat
                   open Categories.Idems cat
               in {ide ide' : Idem}(f : SplitMap cat ide ide') →
               let open SplitMap cat f
                   open Idem ide
               in SplitMap cat ide ide
restsplitmap {_}{_}{X}{ide}{_} f = 
  let open RestCat X
      open Cat cat
      open Categories.Idems cat
      open SplitMap cat f
      open Idem ide
  in 
    record { 
      imap = comp (rest imap) e; 
      mlaw = 
        proof
        comp e (comp (comp (rest imap) e) e)
        ≅⟨ cong (comp e) ass ⟩
        comp e (comp (rest imap) (comp e e))
        ≅⟨ cong (comp e ∘ comp (rest imap)) law ⟩
        comp e (comp (rest imap) e)
        ≅⟨ cong (comp e) R4 ⟩
        comp e (comp e (rest (comp imap e)))
        ≅⟨ sym ass ⟩
        comp (comp e e) (rest (comp imap e))
        ≅⟨ cong (λ y → comp y (rest (comp imap e))) law ⟩
        comp e (rest (comp imap e))
        ≅⟨ sym R4 ⟩
        comp (rest imap) e
        ∎ }

RSplitCat : ∀{a b}{X : RestCat {a}{b}}(E : IdemClass (RestCat.cat X)) → RestCat
RSplitCat {_}{_}{X} E = 
  let open RestCat X
      open Cat cat
      open IdemClass cat E
      open Categories.Idems cat
  in record { 
    cat = SplitCat cat E; 
    rest = λ {ide} {ide'} f → restsplitmap {_}{_}{X} f;
    R1 = λ {ide}{_}{f} → 
      let open SplitMap cat f
          open Idem (fst ide)
      in split≅ cat (splitcomp cat f (restsplitmap {_}{_}{X} f)) f
           (proof
            comp imap (comp (rest imap) e) ≅⟨ sym ass ⟩
            comp (comp imap (rest imap)) e ≅⟨ cong (λ y → comp y e) R1 ⟩
            comp imap e ≅⟨ splitprop cat f ⟩ (imap ∎)); 
    R2 = λ {ide}{_}{_}{g}{f} → 
      let open SplitMap cat f
          open Idem (fst ide)
          open SplitMap cat g renaming (imap to imap')
      in split≅ cat (splitcomp cat (restsplitmap {_}{_}{X} g) 
                                      (restsplitmap {_}{_}{X} f)) 
                       (splitcomp cat (restsplitmap {_}{_}{X} f) 
                                      (restsplitmap {_}{_}{X} g))
           (proof
            comp (comp (rest imap') e) (comp (rest imap) e) ≅⟨
            cong (λ y → comp y (comp (rest imap) e)) (restprop {_}{_}{X} g) ⟩
            comp (comp e (rest imap')) (comp (rest imap) e) ≅⟨ ass ⟩
            comp e (comp (rest imap') (comp (rest imap) e)) ≅⟨
            cong (comp e) (sym ass) ⟩
            comp e (comp (comp (rest imap') (rest imap)) e) ≅⟨
            cong (λ y → comp e (comp y e)) R2 ⟩
            comp e (comp (comp (rest imap) (rest imap')) e) ≅⟨
            cong (comp e) ass ⟩
            comp e (comp (rest imap) (comp (rest imap') e)) ≅⟨ sym ass ⟩
            comp (comp e (rest imap)) (comp (rest imap') e) ≅⟨
            cong (λ y → comp y (comp (rest imap') e)) (sym (restprop {_}{_}{X} f)) ⟩
            (comp (comp (rest imap) e) (comp (rest imap') e) ∎));
    R3 = λ {ide}{_}{_}{f}{g} → 
      let open SplitMap cat f
          open Idem (fst ide)
          open SplitMap cat g renaming (imap to imap')
      in split≅ cat (splitcomp cat (restsplitmap {_}{_}{X} g) 
                                      (restsplitmap {_}{_}{X} f))
                       (restsplitmap {_}{_}{X} (splitcomp cat g 
                                                        (restsplitmap {_}{_}{X} f))) (
        proof
        comp (comp (rest imap') e) (comp (rest imap) e)
        ≅⟨ ass ⟩
        comp (rest imap') (comp e (comp (rest imap) e))
        ≅⟨ cong (comp (rest imap')) (sym ass) ⟩
        comp (rest imap') (comp (comp e (rest imap)) e)
        ≅⟨ cong (λ y → comp (rest imap') (comp y e)) (sym (restprop {_}{_}{X} f)) ⟩
        comp (rest imap') (comp (comp (rest imap) e) e)
        ≅⟨ cong (comp (rest imap')) ass ⟩
        comp (rest imap') (comp (rest imap) (comp  e e))
        ≅⟨ cong (comp (rest imap') ∘ comp (rest imap)) law ⟩
        comp (rest imap') (comp (rest imap) e)
        ≅⟨ sym ass ⟩
        comp (comp (rest imap') (rest imap)) e
        ≅⟨ cong (λ y → comp y e) R3 ⟩
        comp (rest (comp imap' (rest imap))) e
        ≅⟨ cong (λ y → comp (rest (comp y (rest imap))) e) (sym (splitprop cat g)) ⟩
        comp (rest (comp (comp imap' e) (rest imap))) e
        ≅⟨ cong (λ y → comp (rest y) e) ass ⟩
        comp (rest (comp imap' (comp e (rest imap)))) e
        ≅⟨ cong (λ y → comp (rest (comp imap' y)) e) (sym (restprop {_}{_}{X} f)) ⟩
        comp (rest (comp imap' (comp (rest imap) e))) e
        ∎);
    R4 = λ {ide}{ide'}{ide''}{f}{g} → 
      let open SplitMap cat f
          open Idem (fst ide)
          open Idem (fst ide') renaming (e to e')
          open SplitMap cat g renaming (imap to imap')
      in 
        split≅ cat (splitcomp cat (restsplitmap {_}{_}{X} g) f)
                      (splitcomp cat f (restsplitmap {_}{_}{X} (splitcomp cat g f)))
        (proof 
         comp (comp (rest imap') e') imap 
         ≅⟨ ass ⟩ 
         comp (rest imap') (comp e' imap)
         ≅⟨ cong (comp (rest imap')) (splitprop2 cat f) ⟩ 
         comp (rest imap') imap
         ≅⟨ cong (comp (rest imap')) (sym (splitprop cat f)) ⟩
         comp (rest imap') (comp imap e)
         ≅⟨ sym ass ⟩
         comp (comp (rest imap') imap) e
         ≅⟨ cong (λ y → comp y e) R4 ⟩
         comp (comp imap (rest (comp imap' imap))) e
         ≅⟨ ass ⟩
         comp imap (comp (rest (comp imap' imap)) e) 
         ∎) }

-- SplitCat is a split restriction category if the idempotent 
-- class is the class of all restriction idempotents 

import Categories.Monos

RestIdemsClass : ∀{a b}{X : RestCat {a}{b}} → IdemClass (RestCat.cat X)
RestIdemsClass {_}{_}{X} = 
  let open RestCat X
      open Cat cat
      open Categories.Idems cat
      open Lemmata X
      open Categories.Monos cat
  in record { 
    ∈ = λ ide → 
      let open Idem ide
      in e ≅ rest e;
    id∈ = λ {X} → 
      proof
      iden
      ≅⟨ sym (lemiii idmono) ⟩
      rest iden
      ∎ }

.RestIdemIsIdem : ∀{a b}{X : RestCat {a}{b}} → 
                 let open RestCat X
                     open Cat cat
                     open Categories.Idems cat
                 in {ide ide' : Idem}(f : SplitMap cat ide ide') →
                 let open Idem ide
                     open SplitMap cat f
                 in comp (comp (rest imap) e) (comp (rest imap) e) ≅
                    comp (rest imap) e 
RestIdemIsIdem {_}{_}{X}{ide}{ide'} f = 
  let open RestCat X
      open Cat cat
      open Categories.Idems cat
      open Lemmata X
      open SplitMap cat f
      open Idem ide
  in  
    proof
    comp (comp (rest imap) e) (comp (rest imap) e)
    ≅⟨ cong (λ y → comp y (comp (rest imap) e)) (restprop {_}{_}{X} f) ⟩
    comp (comp e (rest imap)) (comp (rest imap) e)
    ≅⟨ ass ⟩
    comp e (comp (rest imap) (comp (rest imap) e))
    ≅⟨ cong (comp e) (sym ass) ⟩
    comp e (comp (comp (rest imap) (rest imap)) e)
    ≅⟨ cong (λ y → comp e (comp y e)) lemii ⟩
    comp e (comp (rest imap) e)
    ≅⟨ cong (comp e) (restprop {_}{_}{X} f) ⟩
    comp e (comp e (rest imap))
    ≅⟨ sym ass ⟩
    comp (comp e e) (rest imap)
    ≅⟨ cong (λ y → comp y (rest imap)) law ⟩
    comp e (rest imap)
    ≅⟨ sym (restprop {_}{_}{X} f) ⟩
    comp (rest imap) e
    ∎

RIdeSplitCat : ∀{a b}{X : RestCat {a}{b}} → SplitRestCat
RIdeSplitCat {_}{_}{X} = 
  let open RestCat X
      open Cat cat
      open Categories.Idems
      open Lemmata
      open IdemClass cat (RestIdemsClass {_}{_}{X})
  in record { 
    rcat = RSplitCat {_}{_}{X} (RestIdemsClass {_}{_}{X}); 
    rsplit = λ {ide}{ide'} f → 
      let open Idem cat (fst ide)
          open SplitMap cat f
          open SplitMap cat (restsplitmap {_}{_}{X} f) renaming (imap to rimap; mlaw to rmlaw)

      
          .rf∈ : ∈ (record { E = E; e = rimap; law = RestIdemIsIdem {_}{_}{X} f })
          rf∈ = 
            proof 
            comp (rest imap) e 
            ≅⟨ cong (comp (rest imap)) (snd ide) ⟩ 
            comp (rest imap) (rest e) 
            ≅⟨ R3 ⟩ 
            rest (comp imap (rest e))
            ≅⟨ cong (rest ∘ comp imap) (sym (snd ide)) ⟩ 
            rest (comp imap e)
            ≅⟨ lemiv X ⟩ 
            rest (comp (rest imap) e) 
            ∎

          rf : Σ' (Idem cat) ∈
          rf = (record { E = E; e = rimap; law = RestIdemIsIdem {_}{_}{X} f } ,, rf∈)

          .smlaw : comp e (comp (comp (comp (rest imap) e) e) (comp (rest imap) e)) ≅ comp (comp (rest imap) e) e
          smlaw = 
              proof
              comp e (comp (comp (comp (rest imap) e) e) (comp (rest imap) e)) 
              ≅⟨ cong (λ y → comp e (comp y (comp (rest imap) e))) ass ⟩ 
              comp e (comp (comp (rest imap) (comp e e)) (comp (rest imap) e)) 
              ≅⟨ cong (λ y → comp e (comp (comp (rest imap) y) (comp (rest imap) e))) law ⟩ 
              comp e (comp (comp (rest imap) e) (comp (rest imap) e)) 
              ≅⟨ cong (comp e) (RestIdemIsIdem {_}{_}{X} f) ⟩ 
              comp e (comp (rest imap) e)
              ≅⟨ sym ass ⟩ 
              comp (comp e (rest imap)) e
              ≅⟨ cong (λ y → comp y e) (sym (restprop {_}{_}{X} f)) ⟩
              comp (comp (rest imap) e) e 
              ∎
          
          s : SplitMap cat (record { E = E; e = comp (rest imap) e; law = RestIdemIsIdem {_}{_}{X} f }) (fst ide)
          s = record { 
            imap = comp rimap e; 
            mlaw = smlaw }

          .rmlaw : comp (comp (rest imap) e) (comp (comp (comp (rest imap) e) e) e) ≅ comp (comp (rest imap) e) e 
          rmlaw = 
              proof
              comp (comp (rest imap) e) (comp (comp (comp (rest imap) e) e) e) 
              ≅⟨ cong (comp (comp (rest imap) e)) ass ⟩ 
              comp (comp (rest imap) e) (comp (comp (rest imap) e) (comp e e)) 
              ≅⟨ cong (λ y → comp (comp (rest imap) e) (comp (comp (rest imap) e) y)) law ⟩ 
              comp (comp (rest imap) e) (comp (comp (rest imap) e) e) 
              ≅⟨ sym ass ⟩ 
              comp (comp (comp (rest imap) e) (comp (rest imap) e)) e 
              ≅⟨ cong (λ y → comp y e) (RestIdemIsIdem {_}{_}{X} f) ⟩ 
              comp (comp (rest imap) e) e 
              ∎

          r : SplitMap cat (fst ide) (record { E = E; e = comp (rest imap) e; law = RestIdemIsIdem {_}{_}{X} f })
          r = record { 
            imap = comp rimap e; 
            mlaw = rmlaw }

          .law1 : comp (comp (comp (rest imap) e) e) (comp (comp (rest imap) e) e) ≅ comp (rest imap) e
          law1 = 
            proof
            comp (comp (comp (rest imap) e) e) (comp (comp (rest imap) e) e) 
            ≅⟨ cong (λ y → comp y (comp (comp (rest imap) e) e)) ass ⟩
            comp (comp (rest imap) (comp e e)) (comp (comp (rest imap) e) e) 
            ≅⟨ cong (λ y → comp (comp (rest imap) y) (comp (comp (rest imap) e) e)) law ⟩
            comp (comp (rest imap) e) (comp (comp (rest imap) e) e) 
            ≅⟨ cong (λ y → comp (comp (rest imap) e) y) ass ⟩
            comp (comp (rest imap) e) (comp (rest imap) (comp e e))
            ≅⟨ cong (λ y → comp (comp (rest imap) e) (comp (rest imap) y)) law ⟩
            comp (comp (rest imap) e) (comp (rest imap) e)
            ≅⟨ RestIdemIsIdem {_}{_}{X} f ⟩
            comp (rest imap) e 
            ∎

      in record { 
        B = rf;
        s = s;
        r = r;
        law1 = split≅ cat (splitcomp cat s r) (restsplitmap {_}{_}{X} f) law1; 
        law2 = split≅ cat (splitcomp cat r s) (splitiden cat {record { E = E; e = comp (rest imap) e; law = RestIdemIsIdem {_}{_}{X} f }}) law1}}


open import RestrictionFunctors

RIncl : ∀{a b}{X : RestCat {a}{b}} → RestFun X (RSplitCat {_}{_}{X} (RestIdemsClass {_}{_}{X}))
RIncl {_}{_}{X} = record { 
  fun = Incl (RestCat.cat X) (RestIdemsClass {_}{_}{X});
  frest = λ {A} {B} {f} → split≅ (RestCat.cat X) _ _ (Cat.idr (RestCat.cat X)) }
