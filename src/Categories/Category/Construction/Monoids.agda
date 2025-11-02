{-# OPTIONS --cubical-compatible --without-K --safe #-}
open import Categories.Category.Core
open import Categories.Category.Monoidal.Core

-- This module defines the category of monoids internal to a given monoidal
-- category.

module Categories.Category.Construction.Monoids {o ℓ e} {𝒞 : Category o ℓ e} (C : Monoidal 𝒞) where

open import Level

open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Object.Monoid C

open Category 𝒞
open Monoidal C
open HomReasoning
open Monoid using (η; μ)
open Monoid⇒

Monoids : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
Monoids = record
  { Obj = Monoid
  ; _⇒_ = Monoid⇒
  ; _≈_ = λ f g → arr f ≈ arr g
  ; id = record
    { arr = id
    ; preserves-μ = identityˡ ○ introʳ (Functor.identity ⊗)
    ; preserves-η = identityˡ
    }
  ; _∘_ = λ f g → record
    { arr = arr f ∘ arr g
    ; preserves-μ = glue (preserves-μ f) (preserves-μ g) ○ ∘-resp-≈ʳ (⟺ (Functor.homomorphism ⊗))
    ; preserves-η = glueTrianglesˡ (preserves-η f) (preserves-η g)
    }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  -- We cannot define equiv = equiv here, because _⇒_ of this category is a
  -- different level to the _⇒_ of 𝒞.
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = ∘-resp-≈
  } where open Equiv
