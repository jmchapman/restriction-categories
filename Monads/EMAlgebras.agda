open import Categories
open import Monads

module Monads.EMAlgebras {a b}(C : Cat {a}{b})(Tm : Monad C) where

  open import Relation.Binary.HeterogeneousEquality
  open import Functors
  open import Utilities
  open Cat C
  open Monad Tm
  open Fun (TFun Tm)
  open import Level

  record Algebra : Set (a ⊔ b) where
    field M       : Obj
          ν       : Hom (T M) M
          .ηlaw    : comp ν η ≅ iden {M}
          .bindlaw : comp ν (HMap ν) ≅ comp ν (μ {M})

  record AlgebraMap (X Y : Algebra) : Set b where
    open Algebra X renaming (ν to νM)
    open Algebra Y renaming (M to N; ν to νN)
    field mhom  : Hom M N
          .mcom : comp mhom νM ≅ comp νN (HMap mhom)
  
  open Algebra
  open AlgebraMap

  .AlgebraMapEq : ∀{X Y}(f g : AlgebraMap X Y) → mhom f ≅ mhom g → f ≅ g
  AlgebraMapEq {X}{Y} f g p = cong₂
    {_}
    {_}
    {_}
    {Hom (M X) (M Y)}
    {λ mhom → comp mhom (ν X) ≅ comp (ν Y) (HMap mhom)}
    {λ _ _ → AlgebraMap X Y}
    {mhom f}
    {mhom g}
    {mcom f}
    {mcom g}    
    (λ x y → record { mhom = x; mcom = y }) 
    p 
    (fixtypes' (cong (λ y → comp y (ν X)) p))
