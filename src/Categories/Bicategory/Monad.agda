{-# OPTIONS --cubical-compatible --without-K --safe #-}

-- A Monad in a Bicategory.
-- For the more elementary version of Monads, see 'Categories.Monad'.
module Categories.Bicategory.Monad where

open import Level
open import Data.Product using (_,_)

open import Categories.Bicategory
import Categories.Bicategory.Extras as Bicat
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)


record Monad {o ℓ e t} (𝒞 : Bicategory o ℓ e t) : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  open Bicat 𝒞

  field
    C : Obj
    T : C ⇒₁ C
    η : id₁ ⇒₂ T
    μ : (T ⊚₀ T) ⇒₂ T

    assoc     : μ ∘ᵥ (T ▷ μ) ∘ᵥ associator.from ≈ (μ ∘ᵥ (μ ◁ T))
    sym-assoc : μ ∘ᵥ (μ ◁ T) ∘ᵥ associator.to ≈ (μ ∘ᵥ (T ▷ μ))
    identityˡ : μ ∘ᵥ (T ▷ η) ∘ᵥ unitorʳ.to ≈ id₂
    identityʳ : μ ∘ᵥ (η ◁ T) ∘ᵥ unitorˡ.to ≈ id₂
