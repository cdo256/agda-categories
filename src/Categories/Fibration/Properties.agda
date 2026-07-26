{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor
-- open import Categories.Fibration.Cartesian
open import Categories.Fibration.Base

module Categories.Fibration.Properties {o ℓ e o′ ℓ′ e′} {𝐄 : Category o ℓ e} {𝐁 : Category o′ ℓ′ e′} (p : Functor 𝐄 𝐁) where

open import Level
open import Data.Product

open import Categories.Morphism 𝐁 using () renaming (_≅_ to _≅ᴮ_)
open import Categories.Morphism 𝐄 using () renaming  (_≅_ to _≅ᴱ_)
open import Categories.Morphism.Cartesian using (Cartesian)

private
  module 𝐄 = Category 𝐄
  module 𝐁 = Category 𝐁
  open Functor p renaming (F₀ to p₀; F₁ to p₁; homomorphism to p-hom)

open import Categories.Morphism using (IsIso)
open import Categories.Bicategory
open import Function.Structures

open import Categories.Fibration.Fiber p using (Fiber; fiberObj₀; FiberObj; FiberHom)

module Fib I = Category (Fiber I)

isoAreCartesian : ∀ (X Y : 𝐄.Obj)
  → (f : X 𝐄.⇒ Y)
  → (isIso-f : IsIso 𝐄 f)
  → Cartesian p f
isoAreCartesian X Y f isIso-f = record
  { universal = λ {Z} {u} h _ → f.inv 𝐄.∘ h
  ; commute = λ {Z} {u} {h} _ → begin
    f 𝐄.∘ (f.inv 𝐄.∘ h)
      ≈⟨ 𝐄.sym-assoc ⟩
    (f 𝐄.∘ f.inv) 𝐄.∘ h
      ≈⟨ 𝐄.∘-resp-≈ˡ f.isoʳ ⟩
    𝐄.id 𝐄.∘ h
      ≈⟨ 𝐄.identityˡ ⟩
    h ∎
  ; compat = λ {Z} {u} {h} q → 𝐁R.begin
    p₁ (f.inv 𝐄.∘ h)
      𝐁R.≈˘⟨ 𝐁.Equiv.sym p-hom ⟩
    p₁ f.inv 𝐁.∘ p₁ h
      𝐁R.≈˘⟨ 𝐁.∘-resp-≈ʳ q ⟩
    p₁ f.inv 𝐁.∘ (p₁ f 𝐁.∘ u)
      𝐁R.≈⟨ 𝐁.sym-assoc ⟩
    (p₁ f.inv 𝐁.∘ p₁ f) 𝐁.∘ u
      𝐁R.≈⟨ 𝐁.∘-resp-≈ˡ (𝐁.Equiv.sym p-hom) ⟩
    p₁ (f.inv 𝐄.∘ f) 𝐁.∘ u
      𝐁R.≈⟨ 𝐁.∘-resp-≈ˡ (F-resp-≈ f.isoˡ) ⟩
    p₁ 𝐄.id 𝐁.∘ u
      𝐁R.≈⟨ 𝐁.∘-resp-≈ˡ identity ⟩
    𝐁.id 𝐁.∘ u
      𝐁R.≈⟨ 𝐁.identityˡ ⟩
    u 𝐁R.∎ }
  where
  module f = IsIso isIso-f
  open 𝐄.HomReasoning
  module 𝐁R = 𝐁.HomReasoning
