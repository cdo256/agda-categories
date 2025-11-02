{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category.Core

-- Kernel Pair - a Pullback of a morphism along itself
-- https://ncatlab.org/nlab/show/kernel+pair
module Categories.Diagram.KernelPair {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Diagram.Pullback 𝒞

open Category 𝒞

private
  variable
    A B : Obj

-- Make it a pure synonym
KernelPair : (f : A ⇒ B) → Set (o ⊔ ℓ ⊔ e)
KernelPair f = Pullback f f
