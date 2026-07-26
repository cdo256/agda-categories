{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor
open import Data.Product

-- Street fibration, which is the version of fibration that respects the principle of equivalence.
-- https://ncatlab.org/nlab/show/Grothendieck+fibration#StreetFibration

-- Adapted from Categories.Functor.Fibration applying the following renaming
--
-- agda-categories | my notation
-- -----------------------------
-- C               | 𝐄
-- D               | 𝐁
-- F               | p
-- A               | I
-- B               | Y
-- f               | u
-- universal₀      | X
-- universal₁      | f
-- iso             | ϕ
-- commute         | u∘φ⁻≈pf
-- cartesian       | cartesian (unchanged)

module Categories.Fibration.Base {o ℓ e o′ ℓ′ e′} {𝐄 : Category o ℓ e} {𝐁 : Category o′ ℓ′ e′} (p : Functor 𝐄 𝐁) where

open import Level

open import Categories.Morphism 𝐁 using (_≅_)
open import Categories.Morphism.Cartesian using (Cartesian)

private
  module 𝐄 = Category 𝐄
  module 𝐁 = Category 𝐁
  open Functor p renaming (F₀ to p₀; F₁ to p₁)

record Fibration : Set (levelOfTerm p) where
  field
    -- X --- f ---> Y
    --
    -- I --- u ---> p₀ Y
    X : ∀ {I Y} (u : I 𝐁.⇒ p₀ Y) → 𝐄.Obj
    f : ∀ {I Y} (u : I 𝐁.⇒ p₀ Y) → X u 𝐄.⇒ Y
    φ : ∀ {I Y} (u : I 𝐁.⇒ p₀ Y) → p₀ (X u) ≅ I

  module φ {I Y} (u : I 𝐁.⇒ p₀ Y) = _≅_ (φ u)

  field
    -- u ∘ φ⁻¹ = p₁ f
    u∘φ⁻≈pf   : ∀ {I Y} (u : I 𝐁.⇒ p₀ Y) → u 𝐁.∘ φ.from u 𝐁.≈ p₁ (f u)
    cartesian : ∀ {I Y} (u : I 𝐁.⇒ p₀ Y) → Cartesian p (f u)

  module cartesian {I Y} (u : I 𝐁.⇒ p₀ Y) = Cartesian (cartesian u)

  open import Categories.Morphism using (IsIso)
  open import Categories.Bicategory
  open import Function.Structures

  1,1,2-1
    : ∀ {X Y}
    → (g : X 𝐄.⇒ Y)
    → Cartesian p g
    → ∀ Z → (v : p₀ Z 𝐁.⇒ p₀ Y)
    → IsBijection (𝐄._≈_ {Z} {X}) (𝐄._≈_ {Z} {Y}) (g 𝐄.∘_)
  1,1,2-1 {X} {Y} g cart-g Z v = record
    { isInjection = record
      { isCongruent = record
        { cong = 𝐄.∘-resp-≈ 𝐄.Equiv.refl
        ; isEquivalence₁ = 𝐄.equiv
        ; isEquivalence₂ = 𝐄.equiv }
      ; injective = λ {h} {i} p → {!!} }
    ; surjective = λ h → {!!} , {!!} }
  1,1,2-2
    : ∀ {X Y}
    → (f : X 𝐄.⇒ Y)
    → (∀ Z → (v : p₀ Z 𝐁.⇒ p₀ Y)
      → IsBijection (𝐄._≈_ {Z} {X}) (𝐄._≈_ {Z} {Y}) (f 𝐄.∘_))
    → Cartesian p f

