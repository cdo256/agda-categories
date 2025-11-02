{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category.Core

-- Reflexive pairs and reflexive coequalizers
-- https://ncatlab.org/nlab/show/reflexive+coequalizer
module Categories.Diagram.ReflexivePair {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Diagram.Coequalizer 𝒞

open Category 𝒞
open HomReasoning
open Equiv

private
  variable
    A B R : Obj

-- A reflexive pair can be thought of as a vast generalization of a reflexive relation.
-- To see this, consider the case in 'Set' where 'R ⊆ A × A', and 'f' and 'g' are the projections.
-- Then, our morphism 's' would have to look something like the diagonal morphism due to the
-- restriction it is a section of both 'f' and 'g'.
record IsReflexivePair (f g : R ⇒ A) (s : A ⇒ R) : Set e where
  field
    sectionₗ : f ∘ s ≈ id
    sectionᵣ : g ∘ s ≈ id

  section : f ∘ s ≈ g ∘ s
  section = sectionₗ ○ ⟺ sectionᵣ

record ReflexivePair (f g : R ⇒ A) : Set (ℓ ⊔ e) where
  field
    s : A ⇒ R
    isReflexivePair : IsReflexivePair f g s

  open IsReflexivePair isReflexivePair public
