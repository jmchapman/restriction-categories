
module Monads.Delay.Zero where

open import Monads.Delay
open import Coinduction
open import RestrictionCat
open import Categories
open import Monads.Kleisli
open Cat (Kl DelayM)
open import RestrictionDelay
open RestCat DelayR

{-
-- Restriction zeros

zero : {A B : Set} → A → Delay B
zero a = never

f0g=0 : ∀{A B C D}(g : C → Delay D)(f : A → Delay B)(a : A) → 
        (comp g zero) (f a) ≈ zero a
f0g=0 g f a with f a
f0g=0 g f a | now b = later≈ (♯ (f0g=0 g f a))
f0g=0 g f a | later b = later≈ (♯ (f0g=0 g f a))

rest0=0 : ∀{A B}(a : A) → rest (zero {B = B}) a ≈ zero a
rest0=0 a = later≈ (♯ (rest0=0 a))
-}