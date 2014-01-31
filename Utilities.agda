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
               (a : A) → (lift {B} f p) (abs a) ≅ f a

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
                                            renaming (lift to lift-map)      
  in lift-map (λ g → abs ∘ g) (λ p → ext (λ a → ax1 _ _ (p a))) f

.map~→~-abs : ∀{A B R} → 
              map~→~ {A}{B}{R} ∘ Quotient.abs (quot (A → B) (EqR→ R)) ≅ 
              (λ (f : A → B) a → Quotient.abs (quot B R) (f a))
map~→~-abs {A}{B}{R} = 
  let open Quotient (quot B R)
      open Quotient (quot (A → B) (EqR→ R)) hiding (abs; ax1)
                                            renaming (lift to lift-map; 
                                                      ax3 to ax3-map)      
  in ext (λ f → ax3-map {λ _ → A → Quotient.Q (quot B R)} 
                        (λ g → abs ∘ g) 
                        (λ p → ext (λ a → ax1 _ _ (p a))) 
                        f)

.map~→~-naturality : ∀{A B C R R'}{f : B → C} →
                     let open Quotient (quot B R) renaming (lift to liftB;
                                                            compat to compatB)
                         open Quotient (quot C R') renaming (Q to QC; abs to absC)
                         open Quotient (quot (A → B) (EqR→ R)) renaming (Q to Q-mapB;
                                                                         lift to lift-mapB;                                                     
                                                                         compat to compat-mapB)
                         open Quotient (quot (A → C) (EqR→ R')) renaming (Q to Q-mapC; 
                                                                          abs to abs-mapC)      
                     in {p : compatB {λ _ → QC} (absC ∘ f)}
                        {q : compat-mapB {λ _ → Q-mapC} (λ l → abs-mapC (f ∘ l))} → 
                        (g : Q-mapB) →
                        liftB {λ _ → QC} (absC ∘ f) p ∘ map~→~ {A}{B}{R} g ≅ 
                        map~→~ {A}{C}{R'} (lift-mapB (λ l → abs-mapC (f ∘ l)) q g)
map~→~-naturality {A}{B}{C}{R}{R'}{f}{p}{q} g = 
  let open Quotient (quot B R) renaming (lift to liftB; 
                                         abs to absB; 
                                         ax3 to ax3B)
      open Quotient (quot C R') renaming (Q to QC; abs to absC)
      open Quotient (quot (A → B) (EqR→ R)) renaming (lift to lift-mapB; 
                                                      abs to abs-mapB;
                                                      ax1 to ax1-mapB;      
                                                      ax3 to ax3-mapB)      
      open Quotient (quot (A → C) (EqR→ R')) renaming (Q to Q-mapC; 
                                                       abs to abs-mapC)      
  in lift-mapB
       {λ y →
          liftB (absC ∘ f) p ∘ map~→~ y ≅
          map~→~ (lift-mapB (λ l → abs-mapC (f ∘ l)) q y)}
       (λ h → 
         proof
         liftB {λ _ → QC} (absC ∘ f) p ∘ map~→~ {A}{B}{R} (abs-mapB h)
         ≅⟨ cong (λ y → liftB {λ _ → QC} (absC ∘ f) p ∘ (y h)) (map~→~-abs {A}{B}{R}) ⟩
         liftB {λ _ → QC} (absC ∘ f) p ∘ absB ∘ h
         ≅⟨ ext (λ a → ax3B (absC ∘ f) p (h a)) ⟩
         absC ∘ (f ∘ h)
         ≅⟨ cong (λ y → y (f ∘ h)) (sym (map~→~-abs {A}{C}{R'}))  ⟩
         map~→~ {A}{C}{R'} (abs-mapC (f ∘ h))
         ≅⟨ cong map~→~ (sym (ax3-mapB (λ l → abs-mapC (f ∘ l)) q h)) ⟩
         map~→~ {A}{C}{R'} (lift-mapB {λ _ → Q-mapC} (λ l → abs-mapC (f ∘ l)) q (abs-mapB h))
         ∎)
       (λ r → fixtypes' (cong (λ y → liftB {λ _ → QC} (absC ∘ f) p ∘ map~→~ y) (ax1-mapB _ _ r)))
       g

.lift-map-abs : ∀{A B R}{f : Quotient.Q (quot (A → B) (EqR→ R))}{x : A} →
               Quotient.lift (quot (A → B) (EqR→ R)) 
                             {λ _ → Quotient.Q (quot B R)} 
                             (λ g → Quotient.abs (quot B R) (g x)) 
                             (λ p → Quotient.ax1 (quot B R) _ _ (p x)) 
                             f ≅
               Quotient.lift (quot (A → B) (EqR→ R)) 
                             {λ _ → A → Quotient.Q (quot B R)}
                             (λ g → Quotient.abs (quot B R) ∘ g) 
                             (λ p → 
                               ext (λ a → Quotient.ax1 (quot B R) _ _ (p a)))
                             f
                             x
lift-map-abs {A}{B}{R}{f}{x} = 
  let open Quotient (quot B R)
      open Quotient (quot (A → B) (EqR→ R)) renaming (Q to Q-map;
                                                      abs to abs-map;
                                                      lift to lift-map; 
                                                      ax1 to ax1-map;      
                                                      ax3 to ax3-map)      
  in Quotient.lift 
       (quot (A → B) (EqR→ R))
       {λ y →
          lift-map {λ _ → Q} (λ g → abs (g x)) (λ p → ax1 _ _ (p x)) y ≅
          lift-map {λ _ → A → Q} 
                   (λ g → abs ∘ g) 
                   (λ p → ext (λ a → ax1 _ _ (p a))) y x}
       (λ h → 
         proof
         lift-map {λ _ → Q} (λ g → abs (g x)) (λ p → ax1 _ _ (p x)) (abs-map h)
         ≅⟨ ax3-map (λ g → abs (g x)) (λ p → ax1 _ _ (p x)) h ⟩
         abs (h x)
         ≅⟨ cong (λ g → g x) 
                 (sym (ax3-map {λ _ → A → Q} 
                               (λ g → abs ∘ g) 
                               (λ p → ext (λ a → ax1 _ _ (p a))) 
                               h)) ⟩
         lift-map {λ _ → A → Q} 
                  (λ g → abs ∘ g) 
                  (λ p → ext (λ a → ax1 _ _ (p a))) 
                  (abs-map h) 
                  x
         ∎)
       (λ r → 
         fixtypes' (cong (lift-map (λ g → abs (g x)) (λ p → ax1 _ _ (p x))) 
                         (ax1-map _ _ r))) 
       f

postulate
  ~→map~ : ∀{A B R} → (A → Quotient.Q (quot B R)) → 
           Quotient.Q (quot (A → B) (EqR→ R))

  ~iso1 : ∀{A B R}{f : Quotient.Q (quot (A → B) (EqR→ R))} →
          ~→map~ (map~→~ {A}{B}{R} f) ≅ f

  ~iso2 : ∀{A B R}{f : (A → Quotient.Q (quot B R))} →
          map~→~ {A}{B}{R} (~→map~ f) ≅ f
{-
postulate 
  quotiso : ∀ {A B R} → 
            Σ ((A → Quotient.Q (quot B R)) → Quotient.Q (quot (A → B) (EqR→ R)))
              (λ H → (∀ f → H (map~→~ f) ≅ f) × 
                     (∀ f → map~→~ {R = R} (H f) ≅ f))
-}

.~→map~-abs : ∀{A B R} → 
              ~→map~ {A}{B}{R} ∘ 
              (λ (f : A → B) a → Quotient.abs (quot B R) (f a)) ≅ 
              Quotient.abs (quot (A → B) (EqR→ R))
~→map~-abs {A}{B}{R} = 
  let open Quotient (quot B R)
      open Quotient (quot (A → B) (EqR→ R)) renaming (lift to lift-map; 
                                                      abs to abs-map)      
  in ext (λ f → 
    proof 
    ~→map~ (λ a → abs (f a)) 
    ≅⟨ cong (λ g → ~→map~ (g f)) (sym map~→~-abs) ⟩
    ~→map~ (map~→~ (abs-map f))
    ≅⟨ ~iso1 ⟩ 
    abs-map f 
    ∎)

.~⇢map~-naturality : ∀{A B C R R'}{f : B → C} →
                     let open Quotient (quot B R) renaming (Q to QB;
                                                            lift to liftB;
                                                            compat to compatB)
                         open Quotient (quot C R') renaming (Q to QC; abs to absC)
                         open Quotient (quot (A → B) (EqR→ R)) renaming (lift to lift-mapB;                                                     
                                                                         compat to compat-mapB)
                         open Quotient (quot (A → C) (EqR→ R')) renaming (Q to Q-mapC; 
                                                                          abs to abs-mapC)      
                     in {p : compatB {λ _ → QC} (absC ∘ f)}
                        {q : compat-mapB {λ _ → Q-mapC} (λ l → abs-mapC (f ∘ l))} → 
                        (g : A → QB) →
                        ~→map~ {A}{C}{R'} (liftB {λ _ → QC} (absC ∘ f) p ∘ g) ≅ 
                        lift-mapB {λ _ → Q-mapC} (λ l → abs-mapC (f ∘ l)) q (~→map~ {A}{B}{R} g)
~⇢map~-naturality {A}{B}{C}{R}{R'}{f}{p}{q} g = 
  let open Quotient (quot B R) renaming (lift to liftB; 
                                         abs to absB; 
                                         ax3 to ax3B)
      open Quotient (quot C R') renaming (Q to QC; abs to absC)
      open Quotient (quot (A → B) (EqR→ R)) renaming (lift to lift-mapB; 
                                                      abs to abs-mapB;
                                                      ax1 to ax1-mapB;      
                                                      ax3 to ax3-mapB)      
      open Quotient (quot (A → C) (EqR→ R')) renaming (Q to Q-mapC; 
                                                       abs to abs-mapC)      
  in 
    proof
    ~→map~ {A}{C}{R'} (liftB {λ _ → QC} (absC ∘ f) p ∘ g)
    ≅⟨ cong
         (λ y → ~→map~ {A} {C} {R'} (liftB {λ _ → QC} (absC ∘ f) p ∘ y))
         (sym ~iso2) ⟩
    ~→map~ {A}{C}{R'} (liftB {λ _ → QC} (absC ∘ f) p ∘ (map~→~ (~→map~ g)))
    ≅⟨ cong ~→map~ (map~→~-naturality (~→map~ g)) ⟩
    ~→map~ {A}{C}{R'} (map~→~ (lift-mapB {λ _ → Q-mapC} (λ l → abs-mapC (f ∘ l)) q (~→map~ g)))
    ≅⟨ ~iso1 ⟩
    lift-mapB {λ _ → Q-mapC} (λ l → abs-mapC (f ∘ l)) q (~→map~ {A}{B}{R} g)
    ∎
