module Everything where

-- Wraps and extends the standard library with extensionality, quotients
open import Utilities

-- Formalisation of basic category theory
open import Categories
open import Categories.Pullbacks
open import Categories.Epis
open import Categories.Isos
open import Categories.Pullbacks.PastingLemmas
open import Categories.Idems
open import Categories.Monos
open import Categories.Splits
open import Categories.Functors
       
-- Restriction Categories
open import Restriction.Cat
open import Restriction.Functors
open import Restriction.SplitRestCats
open import Restriction.Totals
open import Restriction.SplitCatIsRestCat
open import Restriction.Idems
open import Restriction.SplitCatIsSplitRestCat

-- Partial Map Categories
open import PartialMaps.Cat
open import PartialMaps.MonicClasses
open import PartialMaps.Stable

-- Soundness and completeness proofs
open import Soundness
open import Completeness

-- examples
open import Monads
open import Monads.Delay
