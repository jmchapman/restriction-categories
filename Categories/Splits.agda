
open import Categories

module Categories.Splits {ℓ₁ ℓ₂}(X : Cat {ℓ₁}{ℓ₂}) where

open import Utilities
open Cat X
open import Categories.Idems X
open import Categories.Epis X
open import Categories.Isos X
open import Categories.Monos X

record Split (i : Idem) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor split
  open Idem i
  field B         : Obj 
        s         : Hom B E
        r         : Hom E B
        splitLaw1 : comp s r ≅ e
        splitLaw2 : comp r s ≅ iden {B}

sectionIsMono : {i : Idem}(sp : Split i) → Mono (Split.s sp)
sectionIsMono sp {g = g}{h} p = 
  let open Split sp 
  in 
    proof
    g
    ≅⟨ sym idl ⟩
    comp iden g
    ≅⟨ cong (λ x → comp x g) (sym splitLaw2) ⟩
    comp (comp r s) g
    ≅⟨ ass ⟩
    comp r (comp s g)
    ≅⟨ cong (comp r) p ⟩
    comp r (comp s h)
    ≅⟨ sym ass ⟩
    comp (comp r s) h
    ≅⟨ cong (λ x → comp x h) splitLaw2 ⟩
    comp iden h
    ≅⟨ idl ⟩
    h 
    ∎

retractionIsEpi : {i : Idem}(sp : Split i) → Epi (Split.r sp)
retractionIsEpi sp {g = g}{h} p = 
  let open Split sp 
  in
    proof 
    g 
    ≅⟨ sym idr ⟩ 
    comp g iden 
    ≅⟨ cong (comp g) (sym splitLaw2) ⟩ 
    comp g (comp r s) 
    ≅⟨ sym ass ⟩ 
    comp (comp g r) s 
    ≅⟨ cong (λ y → comp y s) p ⟩ 
    comp (comp h r) s 
    ≅⟨ ass ⟩ 
    comp h (comp r s) 
    ≅⟨ cong (comp h) splitLaw2 ⟩ 
    comp h iden 
    ≅⟨ idr ⟩ 
    h 
    ∎

splitMap : {i : Idem}(sp sp' : Split i) → Hom (Split.B sp) (Split.B sp')
splitMap (split _ s _ _ _) (split _ s' r' _ _) = comp r' s

splitsAreIso : {i : Idem}(sp sp' : Split i) → Iso (splitMap sp sp')
splitsAreIso {idem _ e _} (split _ s r p q) (split _ s' r' p' q') =  
  iso (comp r s')
      (proof 
       comp (comp r' s) (comp r s') 
       ≅⟨ ass ⟩ 
       comp r' (comp s (comp r s'))
       ≅⟨ cong (comp r') (sym ass) ⟩ 
       comp r' (comp (comp s r) s')
       ≅⟨ cong (λ f → comp r' (comp f s')) p ⟩ 
       comp r' (comp e s')
       ≅⟨ cong (λ f → comp r' (comp f s')) (sym p') ⟩ 
       comp r' (comp (comp s' r') s')
       ≅⟨ cong (comp r') ass ⟩
       comp r' (comp s' (comp r' s'))
       ≅⟨ cong (comp r' ∘ comp s') q' ⟩
       comp r' (comp s' iden)
       ≅⟨ sym ass ⟩
       comp (comp r' s') iden
       ≅⟨ idr ⟩
       comp r' s'
       ≅⟨ q' ⟩
       iden 
       ∎) 
      (proof 
       comp (comp r s') (comp r' s) 
       ≅⟨ ass ⟩
       comp r (comp s' (comp r' s))
       ≅⟨ cong (comp r) (sym ass) ⟩ 
       comp r (comp (comp s' r') s)
       ≅⟨ cong (λ f → comp r (comp f s)) p' ⟩ 
       comp r (comp e s)
       ≅⟨ cong (λ f → comp r (comp f s)) (sym p) ⟩ 
       comp r (comp (comp s r) s)
       ≅⟨ cong (comp r) ass ⟩
       comp r (comp s (comp r s))
       ≅⟨ cong (comp r ∘ comp s) q ⟩
       comp r (comp s iden)
       ≅⟨ sym ass ⟩
       comp (comp r s) iden
       ≅⟨ idr ⟩
       comp r s
       ≅⟨ q ⟩
       iden 
       ∎)

splitsAreIsoLeftTr : {i : Idem}(sp sp' : Split i) → comp (splitMap sp sp') (Split.r sp) ≅ Split.r sp'
splitsAreIsoLeftTr {idem _ e _} sp sp' =
  let open Split sp
      open Split sp' renaming (s to s'; r to r'; splitLaw1 to splitLaw1'; splitLaw2 to splitLaw2')
  in 
    proof 
    comp (comp r' s) r 
    ≅⟨ ass ⟩ 
    comp r' (comp s r)
    ≅⟨ cong (comp r') splitLaw1 ⟩ 
    comp r' e
    ≅⟨ cong (comp r') (sym splitLaw1') ⟩ 
    comp r' (comp s' r')
    ≅⟨ sym ass ⟩ 
    comp (comp r' s') r'
    ≅⟨ cong (λ f → comp f r') splitLaw2' ⟩ 
    comp iden r'
    ≅⟨ idl ⟩ 
    r'
    ∎

splitsAreIsoRightTr : {i : Idem}(sp sp' : Split i) → comp (Split.s sp') (splitMap sp sp') ≅ Split.s sp
splitsAreIsoRightTr {idem _ e _} sp sp' =
  let open Split sp
      open Split sp' renaming (s to s'; r to r'; splitLaw1 to splitLaw1'; splitLaw2 to splitLaw2')
  in 
    proof 
    comp s' (comp r' s) 
    ≅⟨ sym ass ⟩ 
    comp (comp s' r') s
    ≅⟨ cong (λ f → comp f s) splitLaw1' ⟩ 
    comp e s
    ≅⟨ cong (λ f → comp f s) (sym splitLaw1) ⟩ 
    comp (comp s r) s
    ≅⟨ ass ⟩ 
    comp s (comp r s)
    ≅⟨ cong (comp s) splitLaw2 ⟩ 
    comp s iden
    ≅⟨ idr ⟩ 
    s
    ∎

splitMap≅ : {i i' : Idem} → i ≅ i' → (sp : Split i)(sp' : Split i') → Hom (Split.B sp) (Split.B sp')
splitMap≅ refl = splitMap

splitsAreIso≅ : {i i' : Idem}(p : i ≅ i')(sp : Split i)(sp' : Split i') → Iso (splitMap≅ p sp sp')
splitsAreIso≅ refl = splitsAreIso

splitsAreIsoLeftTr≅ : {i i' : Idem}(p : i ≅ i')(sp : Split i)(sp' : Split i') → 
                       comp (splitMap≅ p sp sp') (Split.r sp) ≅ Split.r sp'
splitsAreIsoLeftTr≅ refl = splitsAreIsoLeftTr

splitsAreIsoRightTr≅ : {i i' : Idem}(p : i ≅ i')(sp : Split i)(sp' : Split i') → 
                        comp (Split.s sp') (splitMap≅ p sp sp') ≅ Split.s sp
splitsAreIsoRightTr≅ refl = splitsAreIsoRightTr
