open import RestrictionCat

module MonicClasses (X : SplitRestCat) where

  open import Categories
  open import Relation.Binary.HeterogeneousEquality
  open import Equality
  open ≅-Reasoning renaming (begin_ to proof_)
  open import Function
  open import Data.Product

  open SplitRestCat X
  open RestCat rcat
  open Cat cat
  open Lemmata rcat
  open Idems cat
  open Totals rcat
  open Tot

  record SRestIde {B E} (s : Tot B E) : Set where
    field As    : Obj
          fs    : Hom E As
          rs    : Hom E B
          .law1s : comp (hom s) rs ≅ rest fs
          .law2s : comp rs (hom s) ≅ iden {B}

  open Monos
  open Isos Total
  open Sections cat
  open import Pullbacks Total

{-
  SRIde→Split : ∀{B E}{s : Tot B E} → (sride : SRestIde s) → 
                let open SRestIde sride
                in Split (record { E = E; e = rest fs; law = lemii })
  SRIde→Split {B}{E}{s} sride = 
    let open SRestIde sride
    in record { 
      B = B; 
      s = hom s; 
      r = rs; 
      law1 = law1s; 
      law2 = law2s }
-}

  .MXmon : ∀{B E}{s : Tot B E} → SRestIde s → Mono Total s
  MXmon {_}{_}{s} sride {_}{g}{h} q = TotEq g h (smon (hom s) (SRestIde.rs sride , SRestIde.law2s sride) (cong hom q))


  MXiso : ∀{B E}{s : Tot B E} → Iso s → SRestIde s
  MXiso {_}{E}{s} (g , p , q) = record { 
    As = E; 
    fs = iden; 
    rs = hom g; 
    law1s =       
      proof
      comp (hom s) (hom g)
      ≅⟨ cong hom p ⟩
      iden
      ≅⟨ sym (lemiii (idmono cat)) ⟩
      rest iden
      ∎; 
    law2s = cong hom q }

 
  .SRIdeProp : ∀{B E}{s : Tot B E} → (sride : SRestIde s) →
    let open SRestIde sride
    in comp (hom s) rs ≅ rest rs
  SRIdeProp {_}{_}{s} sride = 
    let open SRestIde sride
    in 
    proof
    comp (hom s) rs
    ≅⟨ law1s ⟩ 
    rest fs
    ≅⟨ sym lemi ⟩
    rest (rest fs)
    ≅⟨ cong rest (sym law1s) ⟩
    rest (comp (hom s) rs)
    ≅⟨ lemiv ⟩
    rest (comp (rest (hom s)) rs)
    ≅⟨ cong (λ y → rest (comp y rs)) (lemiii (smon (hom s) (SRestIde.rs sride , SRestIde.law2s sride))) ⟩ 
    rest (comp iden rs)
    ≅⟨ cong rest idl ⟩
    rest rs
    ∎


  MXcomp : ∀{B E E'}{s : Tot B E}{s' : Tot E E'} → SRestIde s → 
           SRestIde s' → SRestIde (comptot s' s)
  MXcomp {B}{E}{E'}{s}{s'} sride sride' =
    let open SRestIde sride
        open SRestIde sride' renaming (As to As';
                                       fs to fs';
                                       rs to rs';
                                       law1s to law1s';
                                       law2s to law2s')
     in record { 
       As = B; 
       fs = comp (comp rs rs') (rest rs'); 
       rs = comp rs rs'; 
       law1s = 
         proof
         comp (comp (hom s') (hom s)) (comp rs rs')
         ≅⟨ ass ⟩
         comp (hom s') (comp (hom s) (comp rs rs'))
         ≅⟨ cong (comp (hom s')) (sym ass) ⟩
         comp (hom s') (comp (comp (hom s) rs) rs')
         ≅⟨ cong (λ y → comp (hom s') (comp y rs')) (SRIdeProp sride) ⟩
         comp (hom s') (comp (rest rs) rs')
         ≅⟨ cong (comp (hom s')) R4 ⟩
         comp (hom s') (comp rs' (rest (comp rs rs')))
         ≅⟨ sym ass ⟩
         comp (comp (hom s') rs') (rest (comp rs rs'))
         ≅⟨ cong (λ y → comp y (rest (comp rs rs'))) (SRIdeProp sride') ⟩
         comp (rest rs') (rest (comp rs rs'))
         ≅⟨ R2 ⟩
         comp (rest (comp rs rs')) (rest rs')
         ≅⟨ R3 ⟩
         rest (comp (comp rs rs') (rest rs'))
         ∎ ;
       law2s = 
         proof
         comp (comp rs rs') (comp (hom s') (hom s))
         ≅⟨ ass ⟩
         comp rs (comp rs' (comp (hom s') (hom s)))
         ≅⟨ cong (comp rs) (sym ass) ⟩
         comp rs (comp (comp rs' (hom s')) (hom s))
         ≅⟨ cong (λ y → comp rs (comp y (hom s))) law2s' ⟩
         comp rs (comp iden (hom s))
         ≅⟨ cong (comp rs) idl ⟩
         comp rs (hom s)
         ≅⟨ law2s ⟩
         iden
         ∎}

  MXpul : ∀{A B C}(ft : Tot C B){mt : Tot A B} → SRestIde mt → 
          Σ (Pullback ft mt) λ p → 
          let open Pullback p
              open Square sq renaming (h to mt')
          in SRestIde mt'
  MXpul {A}{B}{C} ft {mt} sride = 
    let open SRestIde sride renaming (fs to u; 
                                      rs to r; 
                                      law1s to law1e; 
                                      law2s to law2e)
        open Tot mt renaming (hom to m; tot to mp)
        open Tot ft renaming (hom to f; tot to fp)

        e : Hom B B
        e = rest u

        e' : Hom C C
        e' = rest (comp e f)

        open Split (rsplit (comp e f)) renaming (B to D; 
                                                 s to m'; 
                                                 r to r';
                                                 law1 to law1e';
                                                 law2 to law2e')
        .mp' : _
        mp' = lemiii (smon m' ((r' , law2e')))
        
        mt' : Tot D C
        mt' = record {
          hom = m';
          tot = mp'}

        f' : Hom D A
        f' = comp r (comp f m')
  
        .fp' : rest f' ≅ iden
        fp' =
          proof
          rest (comp r (comp f m'))
          ≅⟨ cong rest (sym idl) ⟩
          rest (comp iden (comp r (comp f m')))
          ≅⟨ cong (λ y → rest (comp y (comp r (comp f m')))) (sym mp) ⟩
          rest (comp (rest m) (comp r (comp f m')))
          ≅⟨ sym lemiv ⟩
          rest (comp m (comp r (comp f m')))
          ≅⟨ cong rest (sym ass) ⟩
          rest (comp (comp m r) (comp f m'))
          ≅⟨ cong (λ y → rest (comp y (comp f m'))) law1e ⟩
          rest (comp e (comp f m'))
          ≅⟨ cong rest (sym ass) ⟩
          rest (comp (comp e f) m')
          ≅⟨ lemiv ⟩
          rest (comp e' m')
          ≅⟨ cong (λ y → rest (comp y m')) (sym law1e') ⟩
          rest (comp (comp m' r') m')
          ≅⟨ cong rest ass ⟩
          rest (comp m' (comp r' m'))
          ≅⟨ cong (λ y → rest (comp m' y)) law2e' ⟩
          rest (comp m' iden)
          ≅⟨ cong rest idr ⟩
          rest m'
          ≅⟨ mp' ⟩
          iden
          ∎

        ft' : Tot D A
        ft' = record {
          hom = f';
          tot = fp'}        

        .sqscom : comp f m' ≅ comp m f'
        sqscom = 
            proof 
            comp f m' 
            ≅⟨ sym idr ⟩ 
            comp (comp f m') iden
            ≅⟨ cong (comp (comp f m')) (sym law2e') ⟩ 
            comp (comp f m') (comp r' m')
            ≅⟨ ass ⟩ 
            comp f (comp m' (comp r' m'))
            ≅⟨ cong (comp f) (sym ass) ⟩ 
            comp f (comp (comp m' r') m')
            ≅⟨ cong (λ y → comp f (comp y m')) law1e' ⟩ 
            comp f (comp (rest (comp e f)) m')
            ≅⟨ sym ass ⟩ 
            comp (comp f (rest (comp e f))) m'
            ≅⟨ cong (λ y → comp y m') (sym R4) ⟩ 
            comp (comp (rest e) f) m'
            ≅⟨ cong (λ y → comp (comp y f) m') lemi ⟩ 
            comp (comp e f) m'
            ≅⟨ cong (λ y → comp (comp y f) m') (sym law1e) ⟩ 
            comp (comp (comp m r) f) m'
            ≅⟨ ass ⟩ 
            comp (comp m r) (comp f m')
            ≅⟨ ass ⟩ 
            comp m f' 
            ∎ 

        sq : Square ft mt
        sq = record { 
          W = D; 
          h = mt';
          k = ft';
          scom = TotEq (comptot ft mt') (comptot mt ft') sqscom}

        prop : (sq' : Square ft mt) →
               Σ' (PMap sq' sq) λ u → (u' : PMap sq' sq) → PMap.mor u ≅  PMap.mor u'
        prop sq' = 
          let open Square sq' renaming (W to D';
                                        h to xt;
                                        k to yt;
                                        scom to scom')

              open Tot xt renaming (hom to x; tot to xp)
              open Tot yt renaming (hom to y; tot to yp)

              α : Hom D' D
              α = comp r' x

              .αprop2 : comp f' α ≅ y
              αprop2 = smon m (r , law2e) 
                  (proof
                   comp m (comp (comp r (comp f m')) (comp r' x))
                   ≅⟨ cong (comp m) ass ⟩
                   comp m (comp r (comp (comp f m') (comp r' x)))
                   ≅⟨ sym ass ⟩
                   comp (comp m r) (comp (comp f m') (comp r' x))
                   ≅⟨ cong (λ y → comp y (comp (comp f m') (comp r' x))) law1e ⟩
                   comp e (comp (comp f m') (comp r' x))
                   ≅⟨ cong (comp e) ass ⟩
                   comp e (comp f (comp m' (comp r' x)))
                   ≅⟨ cong (comp e ∘ comp f) (sym ass) ⟩
                   comp e (comp f (comp (comp m' r') x))
                   ≅⟨ cong (λ y → comp e (comp f (comp y x))) law1e' ⟩
                   comp e (comp f (comp (rest (comp e f)) x))
                   ≅⟨ sym ass ⟩
                   comp (comp e f) (comp (rest (comp e f)) x)
                   ≅⟨ sym ass ⟩
                   comp (comp (comp e f) (rest (comp e f))) x
                   ≅⟨ cong (λ y → comp y x) R1 ⟩
                   comp (comp e f) x
                   ≅⟨ ass ⟩
                   comp e (comp f x)
                   ≅⟨ cong (comp e) (cong hom scom') ⟩
                   comp e (comp m y)
                   ≅⟨ cong (λ z → comp z (comp m y)) (sym law1e) ⟩
                   comp (comp m r) (comp m y)
                   ≅⟨ ass ⟩
                   comp m (comp r (comp m y))
                   ≅⟨ cong (comp m) (sym ass) ⟩
                   comp m (comp (comp r m) y)
                   ≅⟨ cong (λ z → comp m (comp z y)) law2e  ⟩
                   comp m (comp iden y)
                   ≅⟨ cong (comp m) idl ⟩
                   comp m y
                   ∎)

              .αprop : comp m' α ≅ x
              αprop = 
                  proof
                  comp m' α
                  ≅⟨ sym ass ⟩
                  comp (comp m' r') x
                  ≅⟨ cong (λ z → comp z x) law1e' ⟩
                  comp (rest (comp e f)) x
                  ≅⟨ R4 ⟩
                  comp x (rest (comp (comp e f) x)) 
                  ≅⟨ cong (comp x ∘ rest) ass ⟩
                  comp x (rest (comp e (comp f x))) 
                  ≅⟨ cong (comp x ∘ rest ∘ comp e) (cong hom scom') ⟩
                  comp x (rest (comp e (comp m y))) 
                  ≅⟨ cong (λ z → comp x (rest (comp z (comp m y)))) (sym law1e) ⟩
                  comp x (rest (comp (comp m r) (comp m y))) 
                  ≅⟨ cong (comp x ∘ rest) ass ⟩
                  comp x (rest (comp m (comp r (comp m y)))) 
                  ≅⟨ cong (comp x ∘ rest ∘ comp m) (sym ass) ⟩
                  comp x (rest (comp m (comp (comp r m) y))) 
                  ≅⟨ cong (λ z → comp x (rest (comp m (comp z y)))) law2e  ⟩
                  comp x (rest (comp m (comp iden y))) 
                  ≅⟨ cong (comp x ∘ rest ∘ comp m) idl ⟩
                  comp x (rest (comp m y)) 
                  ≅⟨ cong (comp x) lemiv ⟩
                  comp x (rest (comp (rest m) y)) 
                  ≅⟨ cong (λ z → comp x (rest (comp z y))) mp ⟩
                  comp x (rest (comp iden y)) 
                  ≅⟨ cong (comp x ∘ rest) idl ⟩
                  comp x (rest y) 
                  ≅⟨ cong (comp x) yp ⟩
                  comp x iden 
                  ≅⟨ idr ⟩
                  x
                  ∎

              .αp : rest α ≅ iden
              αp =
                     proof
                     rest (comp r' x)
                     ≅⟨ cong rest (sym idl) ⟩
                     rest (comp iden (comp r' x))
                     ≅⟨ cong (λ y → rest (comp y (comp r' x))) (sym mp') ⟩
                     rest (comp (rest m') (comp r' x))
                     ≅⟨ sym lemiv ⟩
                     rest (comp m' (comp r' x))
                     ≅⟨ cong rest αprop ⟩
                     rest x
                     ≅⟨ xp ⟩
                     iden
                     ∎
        
              αt : Tot (Square.W sq') D
              αt = record {
                hom = α;
                tot = αp}
           
              αpmap : PMap sq' sq
              αpmap = record {
                mor = αt;
                prop1 = TotEq (comptot mt' αt) xt αprop;
                prop2 = TotEq (comptot ft' αt) yt αprop2}
          in αpmap ,,
               (λ umap' →
                  let open PMap umap' renaming (mor to ut')
                      open Tot ut' renaming (hom to u')
                  in TotEq αt ut'
                     (smon m' (r' , law2e')
                      (proof
                       comp m' α 
                       ≅⟨ αprop ⟩
                       x 
                       ≅⟨ cong hom (sym prop1) ⟩
                       comp m' u'
                       ∎)))
    in record { sq = sq; prop = prop} ,
       record { As = B; fs = comp e f; rs = r'; law1s = law1e'; law2s = law2e'}

  open import Stable

  M : StableSys Total
  M = record { 
    ∈ = SRestIde; 
    mon = MXmon;
    iso = λ {_}{_}{s} → MXiso {s = s};
    com = MXcomp; 
    pul = MXpul }




    

