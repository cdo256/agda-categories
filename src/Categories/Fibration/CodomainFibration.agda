{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor
-- open import Categories.Fibration.Cartesian
open import Categories.Fibration.Base
open import Level

module Categories.Fibration.CodomainFibration where

open import Data.Product
open import Categories.Category.Instance.Sets
open import Categories.Category.Construction.Arrow
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

Sets⃗ : ∀ ℓ → Category (suc ℓ) ℓ ℓ
Sets⃗ ℓ = Arrow (Sets ℓ)

cod : ∀ ℓ → Functor (Sets⃗ ℓ) (Sets ℓ)
cod ℓ = record
  { F₀ = cod₀
  ; F₁ = cod₁
  ; identity = λ _ → ≡.refl
  ; homomorphism = λ _ → ≡.refl
  ; F-resp-≈ = λ (_ , r) → r
  }
  where
  cod₀ : Morphism (Sets ℓ) → Set ℓ
  cod₀ = Morphism.cod
  cod₁ : ∀ {A B} → Sets⃗ ℓ [ A , B ] → Sets ℓ [ cod₀ A , cod₀ B ]
  cod₁ f = Morphism⇒.cod⇒ f
