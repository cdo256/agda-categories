{-# OPTIONS --without-K --safe #-}

-- Adapted from Categories.Functor.Fibration applying the following renaming:
-- 
-- agda-categories | my notation
-- -----------------------------
-- C               | 𝐄
-- D               | 𝐁
-- F               | p
-- X               | X
-- Y               | Y
-- A               | Z
-- f               | f
-- h               | g

module Categories.Fibration.Cartesian where

open import Level

open import Categories.Category
open import Categories.Functor

private
  variable
    o ℓ e : Level
    𝐄 𝐁 : Category o ℓ e

record Cartesian (p : Functor 𝐄 𝐁) {X Y} (f : 𝐄 [ X , Y ]) : Set (levelOfTerm p) where
  private
    module 𝐄 = Category 𝐄
    module 𝐁 = Category 𝐁
    open Functor p renaming (F₀ to p₀; F₁ to p₁)
    open 𝐁

  field
    universal : ∀ {Z} {u : p₀ Z ⇒ p₀ X} (g : 𝐄 [ Z , Y ]) →
                  p₁ f ∘ u ≈ p₁ g →  𝐄 [ Z , X ]
    commute   : ∀ {Z} {u : p₀ Z ⇒ p₀ X} {g : 𝐄 [ Z , Y ]}
                  (eq : p₁ f ∘ u ≈ p₁ g) →
                  𝐄 [ 𝐄 [ f ∘ universal g eq ] ≈ g ]
    compat    : ∀ {Z} {u : p₀ Z ⇒ p₀ X} {g : 𝐄 [ Z , Y ]}
                  (eq : p₁ f ∘ u ≈ p₁ g) →
                  p₁ (universal g eq) ≈ u

