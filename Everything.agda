module Everything where

-- Wraps and extends the standard library with extensionality, quotients
open import Utilities

-- Formalisation of basic category theory
open import Categories                -- Section 3.3
open import Categories.Functors       -- Section 3.3
open import Categories.Monos          -- Section 3.4
open import Categories.Isos           -- Section 3.4
open import Categories.Pullbacks      -- Section 3.4
open import Categories.Epis
open import Categories.Pullbacks.PastingLemmas
open import Categories.Idems          -- Section 3.8
open import Categories.Splits         -- Section 3.9
       
-- Restriction Categories
open import Restriction.Cat           -- Section 3.6
open import Restriction.Functors      -- Section 3.6
open import Restriction.Totals        -- Section 3.6
open import Restriction.SplitCatIsRestCat  -- Section 3.8
open import Restriction.Idems         -- Section 3.9
open import Restriction.SplitRestCats -- Section 3.9
open import Restriction.SplitCatIsSplitRestCat -- Section 3.9

-- Partial Map Categories
open import PartialMaps.Stable        -- Section 3.5
open import PartialMaps.Cat           -- Section 3.5
open import PartialMaps.MonicClasses  -- Section 3.10

-- Soundness and completeness proofs
open import Soundness                 -- Section 3.7
open import Completeness              -- Section 3.10

