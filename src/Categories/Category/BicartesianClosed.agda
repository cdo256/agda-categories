{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Category.BicartesianClosed {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Category.CartesianClosed 𝒞
open import Categories.Category.Cocartesian 𝒞

record BicartesianClosed : Set (levelOfTerm 𝒞) where
  field
    cartesianClosed : CartesianClosed
    cocartesian     : Cocartesian
