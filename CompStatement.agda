{-# OPTIONS --type-in-type #-}
open import Restriction.SplitRestCats

module CompStatement (X : SplitRestCat) where

open import Utilities
-- open import Categories
-- open import Restriction.Cat
open import Categories.Functors
open import Restriction.Functors
open SplitRestCat
-- open RestCat rcat
-- open Cat cat
open import Restriction.Totals
-- open import PartialMaps.Stable 
-- open import Categories.Pullbacks
-- open Lemmata rcat
open import PartialMaps.MonicClasses
-- open import PartialMaps.Cat Total SectionsOfRestIdem
open import Soundness
-- open import Categories.Idems cat
-- open import Categories.Splits cat
-- open import Categories.Monos cat
open import Categories.Isos RCCat
-- open import Restriction.Idems rcat
-- open import Restriction.SplitCatIsRestCat rcat
open import Completeness X

Completeness : rcat X ∼ RestPar (Total (rcat X)) (SectionsOfRestIdem X)
Completeness = record { f = {!!} ; g = {!!} ; rinv = {!!} ; linv = {!!} }
-- record {
--   f = RFunct; 
--   g = RFunct2; 
--   rinv = restFunEq (funEq refl (iext HIso1)); 
--   linv = restFunEq (funEq refl (iext HIso2)) }
