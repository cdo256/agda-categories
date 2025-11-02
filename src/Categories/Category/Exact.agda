{-# OPTIONS --cubical-compatible --without-K --safe #-}

-- Exact category (https://ncatlab.org/nlab/show/exact+category)
-- is a regular category
-- in which every internal equivalence is a kernel pair

module Categories.Category.Exact where

open import Level

open import Categories.Category.Core
open import Categories.Diagram.Pullback
open import Categories.Category.Cocartesian
open import Categories.Object.Coproduct
open import Categories.Morphism
open import Categories.Diagram.Coequalizer
open import Categories.Diagram.KernelPair

open import Categories.Category.Regular
open import Categories.Morphism.Regular

open import Categories.Object.InternalRelation

record Exact {o ℓ e : Level} (𝒞 : Category o ℓ e) : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Category 𝒞
  open Pullback
  open Coequalizer
  open Equivalence

  field
    regular    : Regular 𝒞
    quotient   : ∀ {X : Obj} (E : Equivalence 𝒞 X) → Coequalizer 𝒞 (R.p₁ E) (R.p₂ E)
    effective  : ∀ {X : Obj} (E : Equivalence 𝒞 X) → IsPullback 𝒞 (R.p₁ E) (R.p₂ E)
      (arr (quotient E)) (arr (quotient E))
