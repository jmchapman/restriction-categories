{-# OPTIONS --type-in-type #-}
module Utilities where

open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality public
open ≅-Reasoning renaming (begin_ to proof_) public
open import Data.Unit hiding (decSetoid; preorder; setoid; _≤_) public 
open import Data.Product public
open import Function public

postulate 
  ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} → 
        (∀ a → f a ≅ g a) → f ≅ g

postulate 
  iext : {A : Set}{B B' : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
         (∀ a → f {a} ≅ g {a}) → 
         _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

proof-irr : {A B : Set}{x : A}{y : B}(p q : x ≅ y) → p ≅ q
proof-irr refl refl = refl

cong₃ : {A B C D : Set}
        (f : A → B → C → D)
        {a a' : A} → a ≅ a' → 
        {b b' : B} → b ≅ b' → 
        {c c' : C} → c ≅ c' → 
        f a b c ≅ f a' b' c'
cong₃ f refl refl refl = refl

hirL : {A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
      {p : a ≅ a'}{q : a'' ≅ a'''} → a ≅ a'' → p ≅ q
hirL {p = refl}{refl} refl = refl

hirR : {A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
       {p : a ≅ a'}{q : a'' ≅ a'''} → a' ≅ a''' → p ≅ q
hirR {p = refl}{refl} refl = refl

EqR : (A : Set) → Set
EqR A = Σ (Rel A _) (λ R → IsEquivalence R)

open IsEquivalence renaming (refl to irefl; sym to isym; trans to itrans)

record Quotient (A : Set) (R : EqR A) : Set where
  open Σ R renaming (proj₁ to _~_)
  field Q : Set
        abs : A → Q 

  compat : (B : Q → Set) → ((a : A) → B (abs a)) → Set
  compat B f = ∀{a b} → a ~ b → f a ≅ f b
     
  field sound : compat (λ _ → Q) abs
        qelim : (B : Q → Set)(f : (a : A) → B (abs a)) → compat B f →
                (x : Q) → B x
        qbeta : (B : Q → Set)(f : (a : A) → B (abs a))(p : compat B f)
                (a : A) → (qelim B f p) (abs a) ≅ f a

postulate quot : (A : Set)(R : EqR A) → Quotient A R

module QuotientLib {A : Set}{R : EqR A}(q : Quotient A R) where

  open Quotient q

  lift : ∀{B}(f : A → B) → compat _ f → Q → B
  lift = qelim _

  qelimCong : (B B' : Q → Set)
              {f : (a : A) → B (abs a)}{g : (a : A) → B' (abs a)}
              {p : compat B f}{p' : compat B' g} → 
              (∀ a → f a ≅ g a) → ∀ x → qelim B f p x ≅ qelim B' g p' x
  qelimCong B B' {f}{g}{p}{p'} r = 
    qelim (λ z → qelim B f p z ≅ qelim B' g p' z) 
          (λ a → 
            proof
            qelim B f p (abs a)
            ≅⟨ qbeta B f p a ⟩
            f a
            ≅⟨ r a ⟩
            g a
            ≅⟨ sym (qbeta B' g p' a) ⟩
            qelim B' g p' (abs a)
            ∎) 
          (λ s → hirL (cong (qelim B f p) (sound s))) 

  qelimabs≅iden : {x : Q} → lift abs sound x ≅ x
  qelimabs≅iden =
    qelim (λ z → lift abs sound z ≅ z)
          (qbeta _ abs sound) 
          (λ p → hirR (sound p)) 
          _

module Quotient₂Lib {A A' : Set}{R : EqR A}{R' : EqR A'}
                    (q : Quotient A R)(q' : Quotient A' R') where

  open QuotientLib
  open Σ R renaming (proj₁ to _∼_; proj₂ to e)
  open Σ R' renaming (proj₁ to _≈_; proj₂ to e')
  open Quotient q
  open Quotient q' renaming (Q to Q'; abs to abs'; qelim to qelim'; 
                             sound to sound'; qbeta to qbeta')

  compat₂ : (B : Q → Q' → Set)
            (f : (a : A)(a' : A') → B (abs a) (abs' a')) → Set
  compat₂ B f = ∀{a b a' b'} → a ∼ a' → b ≈ b' → f a b ≅ f a' b'

  qelim₂ : (B : Q → Q' → Set)
           (f : (a : A)(a' : A') → B (abs a) (abs' a')) 
           (p : compat₂ B f)(x : Q)(x' : Q') → B x x'
  qelim₂ B f p = 
    let g : (a : A)(x' : Q') → B (abs a) x'
        g a = qelim' (B (abs a)) (f a) (p (irefl e))
    in qelim (λ x → (x' : Q') → B x x') g 
             (λ r → ext (qelimCong q' _ _ (λ _ → p r (irefl e'))))
  
  lift₂ : ∀{B}(f : A → A' → B)(p : compat₂ _ f) → Q → Q' → B
  lift₂ = qelim₂ _ 
  
  qbeta₂ : (B : Q → Q' → Set)
            (f : (a : A)(a' : A') → B (abs a) (abs' a')) 
            (p : compat₂ B f)(a : A)(a' : A') → 
            qelim₂ B f p (abs a) (abs' a') ≅ f a a'
  qbeta₂ B f p a a' = 
    proof
    qelim₂ B f p (abs a) (abs' a')
    ≅⟨ cong (λ g → g (abs' a')) 
            (qbeta (λ x → (x' : Q') → B x x')
                   (λ x → qelim' (B (abs x)) (f x) (p (irefl e)))
                   (λ r → ext (qelimCong q' _ _ (λ _ → p r (irefl e')))) a) ⟩
    qelim' (B (abs a)) (f a) (p (irefl e)) (abs' a')
    ≅⟨ qbeta' (B (abs a)) (f a) (p (irefl e)) a' ⟩
    f a a'
    ∎

module Quotient₃Lib {A A' A'' : Set}{R : EqR A}{R' : EqR A'}
                    {R'' : EqR A''}(q : Quotient A R)
                    (q' : Quotient A' R')(q'' : Quotient A'' R'') where

  open QuotientLib
  open Quotient₂Lib
  open Σ R renaming (proj₁ to _∼_; proj₂ to e)
  open Σ R' renaming (proj₁ to _≈_; proj₂ to e')
  open Σ R'' renaming (proj₁ to _≋_; proj₂ to e'')
  open Quotient q
  open Quotient q' renaming (Q to Q'; abs to abs'; qelim to qelim'; 
                             sound to sound'; qbeta to qbeta')
  open Quotient q'' renaming (Q to Q''; abs to abs''; qelim to qelim''; 
                              sound to sound''; qbeta to qbeta'')

  compat₃ : (B : Q → Q' → Q'' → Set)
            (f : (a : A)(a' : A')(a'' : A'') → 
                 B (abs a) (abs' a') (abs'' a'')) → Set
  compat₃ B f = 
    ∀{a b c a' b' c'} → a ∼ a' → b ≈ b' → c ≋ c' → f a b c ≅ f a' b' c'

  qelim₃ : (B : Q → Q' → Q'' → Set)
           (f : (a : A)(a' : A')(a'' : A'') → 
                B (abs a) (abs' a') (abs'' a'')) →
           compat₃ B f → (x : Q)(x' : Q')(x'' : Q'') → B x x' x''
  qelim₃ B f p = 
    let g : (a : A)(x' : Q')(x'' : Q'') → B (abs a) x' x''
        g a = qelim₂ q' q'' (B (abs a)) (f a) (p (irefl e))
    in qelim (λ x → (x' : Q')(x'' : Q'') → B x x' x'') g 
             (λ r → ext (qelimCong q' _ _ 
               (λ s → ext (qelimCong q'' _ _ 
                                   (λ a → p r (irefl e') (irefl e''))))))

