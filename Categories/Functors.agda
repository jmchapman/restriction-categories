
module Categories.Functors where
open import Utilities
open import Categories
open Cat

record Fun {i j i' j'}(C : Cat {i}{j})(D : Cat {i'}{j'}) : 
           Set (i ⊔ j ⊔ i' ⊔ j') where
  constructor functor
  field OMap   : Obj C → Obj D
        HMap   : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                 HMap (comp C f g) ≅ comp D (HMap f) (HMap g)

open Fun

idFun : ∀{i j}{C : Cat {i}{j}} → Fun C C
idFun {C} = record {OMap = id; HMap = id; fid = refl; fcomp = refl}

○fid : ∀{i j i' j' i'' j''} 
       {C : Cat {i}{j}}{D : Cat {i'}{j'}}{E : Cat {i''}{j''}}
       (G : Fun D E)(F : Fun C D){X : Obj C} →
       HMap G (HMap F (iden C {X})) ≅ iden E {OMap G (OMap F X)}
○fid {C = C}{D}{E} G F =  
  proof
  HMap G (HMap F (iden C)) 
  ≅⟨ cong (HMap G) (fid F) ⟩
  HMap G (iden D)
  ≅⟨ fid G ⟩ 
  iden E 
  ∎ 

○fcomp : ∀{i j i' j' i'' j''} 
         {C : Cat {i}{j}}{D : Cat {i'}{j'}}{E : Cat {i''}{j''}}
         (G : Fun D E)(F : Fun C D)
         {X Y Z : Obj C}{g : Hom C Y Z}{f : Hom C X Y} →
         (HMap G ∘ HMap F) (comp C g f) ≅ 
         comp E ((HMap G ∘ HMap F) g) ((HMap G ∘ HMap F) f)
○fcomp {C = C}{D}{E} G F {g = g}{f} =
  proof
  HMap G (HMap F (comp C g f)) 
  ≅⟨ cong (HMap G) (fcomp F) ⟩ 
  HMap G (comp D (HMap F g) (HMap F f))
  ≅⟨ fcomp G ⟩ 
  comp E (HMap G (HMap F g))(HMap G (HMap F f)) 
  ∎

_○_ : ∀{i j i' j' i'' j''} 
      {C : Cat {i}{j}}{D : Cat {i'}{j'}}{E : Cat {i''}{j''}} → 
      Fun D E → Fun C D → Fun C E
G ○ F = record {
  OMap  = OMap G ∘ OMap F;
  HMap  = HMap G ∘ HMap F;
  fid   = ○fid G F;
  fcomp = ○fcomp G F}

Full : ∀{i j i' j'} 
       {C : Cat {i}{j}}{D : Cat {i'}{j'}}
       (F : Fun C D) → Set (j' ⊔ j ⊔ i)
Full {C = C}{D} F = 
  ∀{A B}{f : Hom D (OMap F A) (OMap F B)} →
    Σ (Hom C A B) λ g → HMap F g ≅ f
  
Faithful : ∀{i j i' j'} 
           {C : Cat {i}{j}}{D : Cat {i'}{j'}}
           (F : Fun C D) → Set (j' ⊔ j ⊔ i)
Faithful {C = C} F = 
  ∀{A B}{f g : Hom C A B} → HMap F f ≅ HMap F g → f ≅ g

funEq : ∀{i j i' j'} 
        {C : Cat {i}{j}}{D : Cat {i'}{j'}}{F₀ G₀ : Obj C → Obj D}
        {F₁ : ∀{X Y} → Hom C X Y → Hom D (F₀ X) (F₀ Y)}
        {G₁ : ∀{X Y} → Hom C X Y → Hom D (G₀ X) (G₀ Y)}
        {p : ∀{X} → F₁ (iden C {X}) ≅ iden D {F₀ X}}
        {p' : ∀{X} → G₁ (iden C {X}) ≅ iden D {G₀ X}}
        {q : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
             F₁ (comp C f g) ≅ comp D (F₁ f) (F₁ g)}
        {q' : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
              G₁ (comp C f g) ≅ comp D (G₁ f) (G₁ g)} →
        (r : F₀ ≅ G₀) → (λ {X}{Y} → subst (λ H → Hom C X Y → Hom D (H X) (H Y)) r F₁) ≅ (λ {X}{Y} → G₁ {X}{Y}) →
        functor {C = C}{D} F₀ F₁ p q ≅ functor {C = C}{D} G₀ G₁ p' q'  
funEq refl refl = 
  cong₂ (functor _ _) 
        (iext (λ _ → proof-irr _ _)) 
        (iext (λ _ → iext (λ _ → iext (λ _ → iext (λ _ → iext (λ _ → proof-irr _ _))))))

-- Cat of Cats
CCat : ∀{i j} → Cat
CCat {i}{j} = record {
  Obj = Cat {i}{j};
  Hom = Fun;
  iden = idFun;
  comp = _○_;
  idl = funEq refl refl ;
  idr = funEq refl refl ;
  ass = funEq refl refl }






-- Equality for functors
{-
.Fun≅ : ∀{C D}{F G : Fun C D} → Fun.OMap F ≅ Fun.OMap G →
       (∀{X Y}(f : Hom C X Y) → Fun.HMap F f ≅ Fun.HMap G f) → F ≅ G
Fun≅ {C}{D}{F}{G} p q = cong₄
  {Obj C → Obj D}
  {λ OMap → ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)}
  {λ OMap HMap → ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}}
  {λ OMap HMap → ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → HMap (comp C f g) ≅ comp D (HMap f) (HMap g)}
  {Fun C D}
  {Fun.OMap F}
  {Fun.OMap G} 
  p
  {Fun.HMap F}
  {Fun.HMap G} 
  (iext (λ X → iext (λ Y → ext q)))
  {Fun.fid F}
  {Fun.fid G}  
  (iext (λ X → hir (q (iden C))))
  {Fun.fcomp F}
  {Fun.fcomp G} 
  (iext (λ X → iext (λ Y → iext (λ Z → iext (λ f → iext (λ g → hir (q (comp C f g))))))))
  λ w x y z → record{OMap = w;HMap = x;fid = y; fcomp = z} 
-}

