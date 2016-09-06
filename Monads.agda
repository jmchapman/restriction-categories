module Monads where

open import Categories
open import Utilities renaming (_≅⟨_⟩_ to _≅[_]_)

record Monad (C : Cat) : Set where
  open Cat C
  field T    : Obj → Obj
        η    : ∀ {X} → Hom X (T X)
        bind : ∀{X Y} → Hom X (T Y) → Hom (T X) (T Y)
        law1 : ∀{X} → bind (η {X}) ≅ iden {T X}
        law2 : ∀{X Y}{f : Hom X (T Y)} → comp (bind f) η ≅ f
        law3 : ∀{X Y Z}{f : Hom X (T Y)}{g : Hom Y (T Z)} →
               bind (comp (bind g) f) ≅ comp (bind g) (bind f)

  μ : ∀{X} → Hom (T (T X)) (T X)
  μ = bind iden

open import Categories.Functors

TFun : ∀{C} → Monad C → Fun C C
TFun {C} M = 
  let open Cat C
      open Monad M
  in record { 
    OMap  = T; 
    HMap  = λ f → bind (comp η f); 
    fid   = 
      proof
      bind (comp η iden)
      ≅[ cong bind idr ]
      bind η
      ≅[ law1 ]
      iden
      ∎;
    fcomp = λ {_}{_}{_}{f}{g} → 
      proof
      bind (comp η (comp f g))
      ≅[ cong bind (sym ass) ]
      bind (comp (comp η f) g)
      ≅[ cong (λ y → bind (comp y g)) (sym law2) ]
      bind (comp (comp (bind (comp η f)) η) g)
      ≅[ cong bind ass ]
      bind (comp (bind (comp η f)) (comp η g))
      ≅[ law3 ]
      comp (bind (comp η f)) (bind (comp η g))
      ∎}

record MHom {C : Cat}(M : Monad C)(N : Monad C) : Set where
  open Cat C
  open Monad M renaming (T to S; η to ηS; bind to bindS; μ to μS)
  open Monad N renaming (η to ηT; bind to bindT; μ to μT)
  field Φ : ∀{X} → Hom (S X) (T X)
        .hlaw1 : ∀{X} → comp Φ (ηS {X}) ≅ ηT {X}
        .hlaw2 : ∀{X} → comp Φ (μS {X}) ≅ 
                        comp μT (comp Φ (bindS (comp ηS (Φ {X}))))

id-mhom : ∀{C}{M : Monad C} → MHom M M
id-mhom {C}{M} = 
  let open Cat C
      open Monad M
  in record { 
       Φ = iden ; 
       hlaw1 = idl ; 
       hlaw2 = 
         proof
         comp iden μ
         ≅[ idl ]
         μ
         ≅[ sym idr ]
         comp μ iden
         ≅[ cong (comp μ) (sym law1) ]
         comp μ (bind η)
         ≅[ cong (λ f → comp μ (bind f)) (sym idr) ]
         comp μ (bind (comp η iden))
         ≅[ cong (comp μ) (sym idl) ]
         comp μ (comp iden (bind (comp η iden)))
         ∎}

