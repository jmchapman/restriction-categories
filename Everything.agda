module Everything where

-- Extensions to the standard library, extensionality, quotients
open import Utilities


-- Formalisation of basic category theory
open import Categories
open import Categories.Sections
open import Categories.Pullbacks
open import Categories.Epis
open import Categories.Isos
open import Categories.Pullbacks.PastingLemmas
open import Categories.Pullbacks.PullbacksLemmas
open import Categories.Idems
open import Categories.Monos
open import Categories.Splits
open import Categories.Sets
open import Categories.Products
open import Categories.ProductCats
open import Categories.Functors
open import Categories.StrongFuns

-- Formalisation of monads
open import Monads
open import Monads.PredicatePart
open import Monads.EMCat
open import Monads.Kleisli
open import Monads.EMAlgebras
open import Monads.Maybe

-- The delay monad
--open import Monads.Delay
--open import Monads.Delay.Independence
--open import Monads.Delay.Decision
--open import Monads.Delay.Iteration
--open import Monads.Delay.Meets
--open import Monads.Delay.Joins
--open import Monads.Delay.Zero
--open import Monads.Delay.Products
--open import Monads.Delay.Order

-- Restriction Categories
open import Restriction.Cat
open import Restriction.Products
open import Restriction.Functors
open import Restriction.Pred
open import Restriction.SplitRestCats
open import Restriction.Totals
open import Restriction.Order
--open import Restriction.Delay
open import Restriction.Maybe

-- Partial Map Categories
open import PartialMaps.Cat
open import PartialMaps.MonicClasses
open import PartialMaps.Stable

-- Soundness and completeness proofs
open import Soundness
open import Completeness

open import Misc.SurjectiveQuotients -- a version of quotients that
                                     -- lead to classical logic
