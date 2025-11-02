{-# OPTIONS --cubical-compatible --without-K --safe #-}

-- Monadic Adjunctions
-- https://ncatlab.org/nlab/show/monadic+adjunction
module Categories.Adjoint.Monadic where

open import Level

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Category.Equivalence
open import Categories.Functor
open import Categories.Monad

open import Categories.Category.Construction.EilenbergMoore
open import Categories.Category.Construction.Properties.EilenbergMoore

private
  variable
    o ℓ e : Level
    𝒞 𝒟 : Category o ℓ e

-- An adjunction is monadic if the adjunction "comes from" the induced monad in some sense.
record IsMonadicAdjunction {L : Functor 𝒞 𝒟} {R : Functor 𝒟 𝒞} (adjoint : L ⊣ R) : Set (levelOfTerm 𝒞 ⊔ levelOfTerm 𝒟) where
  private
    T : Monad 𝒞
    T = adjoint⇒monad adjoint

  field
    Comparison⁻¹ : Functor (EilenbergMoore T) 𝒟
    comparison-equiv : WeakInverse (ComparisonF adjoint) Comparison⁻¹
