{-# OPTIONS --type-in-type #-}
module Utilities where

open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality public
open ≅-Reasoning renaming (begin_ to proof_) public
open import Data.Unit hiding (decSetoid; preorder; setoid; _≤_) public 
open import Data.Product public
open import Function public

record Σ' (A : Set)(B : A → Set) : Set where
    constructor _,,_
    field fst : A
          .snd : B fst
open Σ' public


postulate ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ a → f a ≅ g a) → f ≅ g

postulate iext : {A : Set}{B B' : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
                 (∀ a → f {a} ≅ g {a}) → 
                 _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

data Reveal_is_ {A : Set} (x : Hidden A) (y : A) : Set where
  [_] : (eq : reveal x ≅ y) → Reveal x is y

cong₃ : {A : Set}
        {B : A → Set}
        {C : (a : A) → B a → Set}
        {D : (a : A)(b : B a) → C a b → Set}
        {a a' : A} → a ≅ a' → 
        {b : B a}{b' : B a'} → b ≅ b' → 
        {c : C a b}{c' : C a' b'} → c ≅ c' → 
        (f : (a : A)(b : B a)(c : C a b) → D a b c) → f a b c ≅ f a' b' c'
cong₃ refl refl refl f = refl

cong₄ : {A : Set}
        {B : A → Set}
        {C : (a : A) → B a → Set}
        {D : (a : A) → B a → Set}
        {E : Set}
        {a a' : A} → a ≅ a' → 
        {b : B a}{b' : B a'} → b ≅ b' → 
        {c : C a b}{c' : C a' b'} → c ≅ c' → 
        {d : D a b}{d' : D a' b'} → d ≅ d' → 
        (f : (a : A)(b : B a) → C a b → D a b → E) → f a b c d ≅ f a' b' c' d'
cong₄ refl refl refl refl f = refl

inspect : ∀ {A : Set} {B : A → Set}
          (f : (x : A) → B x) (x : A) → Reveal (hide f x) is (f x)
inspect f x = [ refl ]

fixtypes' : {A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
            {p : a ≅ a'}{q : a'' ≅ a'''} →
            a ≅ a'' → p ≅ q
fixtypes' {p = refl} {refl} refl = refl

fixtypes'' : {A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
             {p : a ≅ a'}{q : a'' ≅ a'''} →
              a' ≅ a''' → p ≅ q
fixtypes'' {p = refl}{q = refl} refl = refl

EqR : (A : Set) → Set
EqR A = Σ (Rel A _) (λ R → IsEquivalence R)

open IsEquivalence renaming (refl to irefl; sym to isym; trans to itrans)

record Quotient (A : Set) (R : EqR A) : Set where
  open Σ R renaming (proj₁ to _~_)
  field Q : Set
        abs : A → Q 

  compat : {B : Q → Set} → ((a : A) → B (abs a)) → Set
  compat f = ∀{a b} → a ~ b → f a ≅ f b
     
  field lift : {B : Q → Set}(f : (a : A) → B (abs a)) → .(compat {B} f) →
               (q : Q) → B q
        .ax1 : (a b : A) → a ~ b → abs a ≅ abs b
        ax2 : (a b : A) → abs a ≅ abs b → a ~ b
        .ax3 : {B : Q → Set}(f : (a : A) → B (abs a))(p : compat {B} f)
               (a : A) →  (lift {B} f p) (abs a) ≅ f a

postulate quot : (A : Set) (R : EqR A) → Quotient A R

compat₂ : ∀{A A' B}(R : EqR A)(R' : EqR A') → (A → A' → B) → Set
compat₂ R R' f = 
  let open Σ R renaming (proj₁ to _~_) 
      open Σ R' renaming (proj₁ to _≈_) 
  in ∀{a b a' b'} → a ~ a' → b ≈ b' → f a b ≅ f a' b'

lift₂ : ∀{A A' B R R'}(q : Quotient A R)(q' : Quotient A' R')
        (f : A → A' → B) → .(compat₂ R R' f) → Quotient.Q q → Quotient.Q q' → B
lift₂ {A}{A'}{B}{R}{R'} q q' f p = 
  let open Σ R renaming (proj₁ to _~_; proj₂ to e) 
      open Σ R' renaming (proj₁ to _≈_; proj₂ to e')
      open Quotient q 
      open Quotient q' renaming (Q to Q'; abs to abs'; lift to lift')
  
      g : A → Q' → B
      g a = lift' (f a) (p (irefl e))

      .fa≅fb : ∀{a b : A} → a ~ b → f a ≅ f b
      fa≅fb r = ext (λ a' → p r (irefl e'))

      conglift : (x y : A' → B)
                 (p : ∀{b b'} → b ≈ b' → x b ≅ x b') → 
                 (p' : ∀{b b'} → b ≈ b' → y b ≅ y b') → 
                 (a b : A) → x ≅ y → 
                 lift' x p ≅ lift' y p'
      conglift x y p p' a b q = cong₂ 
        {_}
        {_}
        {_}
        {_}
        {λ x → {b b' : A'} → b ≈ b' → x b ≅ x b'}
        {_}
        {_}
        {_}
        {p}
        {p'} 
        (lift' {λ _ → B}) 
        q 
        (iext λ (a' : A') → iext λ (b' : A') → ext λ (r : a' ≈ b') → fixtypes'
          (cong (λ h → h a') q))

  in lift g (λ {a b} r → conglift 
    (f a) 
    (f b) 
    (p (irefl e)) 
    (p (irefl e)) 
    a 
    b 
    (fa≅fb r))

.liftabs≅iden : ∀{A R}(q : Quotient A R) → 
               let open Quotient q
               in (x : Q) → lift {λ _ → Q} abs (ax1 _ _) x ≅ x
liftabs≅iden q x = 
  let open Quotient q
  in lift 
    {λ y → lift {λ _ → Q} abs (ax1 _ _) y ≅ y} 
    (ax3 abs (ax1 _ _)) 
    (λ p → fixtypes'' (ax1 _ _ p)) 
    x


.lift₂→lift : ∀{A A' B R R'}(q : Quotient A R)(q' : Quotient A' R')
             (f : A → A' → B)(p : compat₂ R R' f)(x : A)
             (x' : Quotient.Q q') → 
             lift₂ q q' f p (Quotient.abs q x) x' ≅ 
             Quotient.lift q' (f x) (p (IsEquivalence.refl (proj₂ R))) x' 
lift₂→lift {A}{A'}{B}{R}{R'} q q' f p x x' = 
  let open Σ R renaming (proj₁ to _~_; proj₂ to e) 
      open Σ R' renaming (proj₁ to _≈_; proj₂ to e')
      open Quotient q 
      open Quotient q' renaming (Q to Q'; 
                                 abs to abs'; 
                                 lift to lift'; 
                                 ax3 to ax3')

      conglift : (x y : A' → B)
                 (p : ∀{b b'} → b ≈ b' → x b ≅ x b') → 
                 (p' : ∀{b b'} → b ≈ b' → y b ≅ y b') → 
                 (a b : A) → x ≅ y → 
                 lift' x p ≅ lift' y p'
      conglift x y p p' a b q = cong₂ 
        {_}
        {_}
        {_}
        {_}
        {λ x → {b b' : A'} → b ≈ b' → x b ≅ x b'}
        {_}
        {_}
        {_}
        {p}
        {p'} 
        (lift' {λ _ → B}) 
        q 
        (iext λ (a' : A') → iext λ (b' : A') → ext λ (r : a' ≈ b') → fixtypes'
          (cong (λ h → h a') q))

      s : ∀{a b} → a ~ b → 
          lift' (f a) (λ r → p (irefl e) r) ≅ lift' (f b) (λ r → p (irefl e) r)
      s {a}{b} r = conglift 
        (f a) 
        (f b) 
        (p (irefl e))
        (p (irefl e)) 
        a 
        b
        (ext (λ _ → p r (irefl e'))) 

  in 
    proof
    lift (λ a → lift' (f a) (p (irefl e))) s (abs x) x'
    ≅⟨ cong (λ g → g x') (ax3 (λ a → lift' (f a) (p (irefl e))) s x) ⟩
    lift' (f x) (λ r → p (irefl e) r) x'
    ∎

.lift₂→lift' : ∀{A A' B R R'}(q : Quotient A R)(q' : Quotient A' R')
               (f : A → A' → B)(p : compat₂ R R' f)(x : Quotient.Q q)
               (x' : A') →
               lift₂ q q' f p x (Quotient.abs q' x') ≅ 
               Quotient.lift q 
                             (λ a → f a x') 
                             (λ r → p r (irefl (proj₂ R')))
                             x
lift₂→lift' {A}{A'}{B}{R}{R'} q q' f p x x' = 
  let open Σ R renaming (proj₁ to _~_; proj₂ to e) 
      open Σ R' renaming (proj₁ to _≈_; proj₂ to e')
      open Quotient q 
      open Quotient q' renaming (Q to Q'; 
                                 abs to abs'; 
                                 lift to lift'; 
                                 ax3 to ax3')

      conglift : (x y : A' → B)
                 (p : ∀{b b'} → b ≈ b' → x b ≅ x b') → 
                 (p' : ∀{b b'} → b ≈ b' → y b ≅ y b') → 
                 (a b : A) → x ≅ y → 
                 lift' x p ≅ lift' y p'
      conglift x y p p' a b q = cong₂ 
        {_}
        {_}
        {_}
        {_}
        {λ x₁ → {b₁ b' : A'} → b₁ ≈ b' → x₁ b₁ ≅ x₁ b'}
        {_}
        {_}
        {_}
        {p}
        {p'} 
        (lift' {λ _ → B}) 
        q 
        (iext λ (a' : A') → iext λ (b' : A') → ext λ (r : a' ≈ b') → fixtypes'
          (cong (λ h → h a') q))

      s : ∀{a b} → a ~ b → 
          lift' (f a) (λ r → p (irefl e) r) ≅ lift' (f b) (λ r → p (irefl e) r)
      s {a}{b} r = conglift 
        (f a) 
        (f b) 
        (p (irefl e))
        (p (irefl e)) 
        a
        b
        (ext (λ a' → p r (irefl e'))) 

  in lift {λ y → lift₂ q q' f p y (abs' x') 
                 ≅ 
                 lift (λ a → f a x') (λ r → p r (irefl e')) y}
          (λ a → 
            proof
            lift₂ q q' f p (abs a) (abs' x')
            ≅⟨ lift₂→lift q q' f p a (abs' x') ⟩
            lift' (f a) (p (irefl e)) (abs' x')
            ≅⟨ ax3' (f a) (p (irefl e)) x' ⟩
            f a x'
            ≅⟨ sym (ax3 (λ b → f b x') (λ r → p r (irefl e')) a) ⟩
            lift (λ b → f b x') (λ r → p r (irefl e')) (abs a)
            ∎) 
          (λ {a b} r → fixtypes' 
            (proof
             lift (λ a₁ → lift' (f a₁) (p (irefl e))) s (abs a) (abs' x')
             ≅⟨ cong (λ g → g (abs' x')) 
                     (ax3 (λ a₁ → lift' (f a₁) (p (irefl e))) s a) ⟩
             lift' (f a) (p (irefl e)) (abs' x')
             ≅⟨ ax3' (f a) (p (irefl e)) x' ⟩
             f a x'
             ≅⟨ p r (irefl e') ⟩
             f b x'
             ≅⟨ sym (ax3' (f b) (p (irefl e)) x') ⟩
             lift' (f b) (p (irefl e)) (abs' x')
             ≅⟨ sym (cong (λ g → g (abs' x')) 
                          (ax3 (λ a₁ → lift' (f a₁) (p (irefl e))) s b)) ⟩
             lift (λ a₁ → lift' (f a₁) (p (irefl e))) s (abs b) (abs' x')
             ∎))
          x

-- introducing the axiom (A → B)/∼' ≅ A → B/~

map~ : ∀{A B}(R : EqR B)(f g : A → B) → Set
map~ (_~_ , _) f g = ∀ x → f x ~ g x  

refl-map~ : ∀{A B R}{f : A → B} → map~ R f f
refl-map~ {R = _ , p} x = irefl p

sym-map~ : ∀{A B R}{f g : A → B} → map~ R f g → map~ R g f
sym-map~ {R = _ , p} q x = isym p (q x)

trans-map~ : ∀{A B R}{f g h : A → B} → map~ R f g → map~ R g h → map~ R f h
trans-map~ {R = _ , p} q r x = itrans p (q x) (r x)

EqR→ : ∀{A B}(R : EqR B) → EqR (A → B)
EqR→ R = map~ R , 
             record { 
               refl = refl-map~ {R = R} ; 
               sym = sym-map~ {R = R} ; 
               trans = trans-map~ {R = R} }

map~→~ : ∀{A B R} → Quotient.Q (quot (A → B) (EqR→ R)) → 
         A → Quotient.Q (quot B R)
map~→~ {A}{B}{R} f = 
  let open Quotient (quot B R)
      open Quotient (quot (A → B) (EqR→ R)) hiding (abs; ax1)
                                                renaming (lift to mlift)      
  in mlift (λ g → abs ∘ g) (λ p → ext (λ a → ax1 _ _ (p a))) f

postulate 
  quotiso : ∀ {A B R} → 
            Σ ((A → Quotient.Q (quot B R)) → Quotient.Q (quot (A → B) (EqR→ R)))
              (λ H → (∀ f → H (map~→~ f) ≅ f) × 
                     (∀ f → map~→~ {R = R} (H f) ≅ f))