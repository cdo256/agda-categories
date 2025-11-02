{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category

-- The core of a category.
-- See https://ncatlab.org/nlab/show/core

module Categories.Category.Construction.Core {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (_⊔_)
open import Function using (flip)

open import Categories.Category.Groupoid using (Groupoid; IsGroupoid)
open import Categories.Morphism 𝒞 as Morphism
open import Categories.Morphism.IsoEquiv 𝒞 as IsoEquiv

open Category 𝒞
open _≃_

Core : Category o (ℓ ⊔ e) e
Core = record
  { Obj       = Obj
  ; _⇒_       = _≅_
  ; _≈_       = _≃_
  ; id        = ≅.refl
  ; _∘_       = flip ≅.trans
  ; assoc     = ⌞ assoc     ⌟
  ; sym-assoc = ⌞ sym-assoc ⌟
  ; identityˡ = ⌞ identityˡ ⌟
  ; identityʳ = ⌞ identityʳ ⌟
  ; identity² = ⌞ identity² ⌟
  ; equiv     = ≃-isEquivalence
  ; ∘-resp-≈  = λ where ⌞ eq₁ ⌟ ⌞ eq₂ ⌟ → ⌞ ∘-resp-≈ eq₁ eq₂ ⌟
  }

Core-isGroupoid : IsGroupoid Core
Core-isGroupoid = record
  { _⁻¹ = ≅.sym
  ; iso = λ {_ _ f} → record { isoˡ = ⌞ isoˡ f ⌟ ; isoʳ = ⌞ isoʳ f ⌟ }
  }
  where open _≅_

CoreGroupoid : Groupoid o (ℓ ⊔ e) e
CoreGroupoid = record { category = Core; isGroupoid = Core-isGroupoid }

module CoreGroupoid = Groupoid CoreGroupoid

-- Useful shorthands for reasoning about isomorphisms and morphisms of
-- 𝒞 in the same module.

module Shorthands where
  module Commutationᵢ where
    open Commutation Core public using () renaming ([_⇒_]⟨_≈_⟩ to [_≅_]⟨_≈_⟩)

    infixl 2 connectᵢ
    connectᵢ : ∀ {A C : Obj} (B : Obj) → A ≅ B → B ≅ C → A ≅ C
    connectᵢ B f g = ≅.trans f g

    syntax connectᵢ B f g = f ≅⟨ B ⟩ g

  open _≅_ public
  open _≃_ public
  open Morphism public using (module _≅_)
  open IsoEquiv public using (⌞_⌟) renaming (module _≃_ to _≈ᵢ_)
  open CoreGroupoid public using (_⁻¹) renaming
    ( _⇒_                 to _≅_
    ; _≈_                 to _≈ᵢ_
    ; id                  to idᵢ
    ; _∘_                 to _∘ᵢ_
    ; iso                 to ⁻¹-iso
    ; module Equiv        to Equivᵢ
    ; module HomReasoning to HomReasoningᵢ
    ; module iso          to ⁻¹-iso
    )
