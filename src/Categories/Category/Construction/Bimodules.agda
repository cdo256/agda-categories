{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Bicategory
open import Categories.Bicategory.Monad using (Monad)

module Categories.Category.Construction.Bimodules {o ℓ e t} {𝒞 : Bicategory o ℓ e t} (M₁ M₂ : Monad 𝒞) where

open import Level
open import Categories.Category
open import Categories.Bicategory.Monad.Bimodule using (Bimodule)
open import Categories.Bicategory.Monad.Bimodule.Homomorphism using (Bimodulehomomorphism; id-bimodule-hom; bimodule-hom-∘)
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞

Bimodules : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
Bimodules = record
  { Obj = Bimodule M₁ M₂
  ; _⇒_ = Bimodulehomomorphism
  ; _≈_ = λ h₁ h₂ → α h₁ ≈ α h₂
  ; id = id-bimodule-hom
  ; _∘_ = bimodule-hom-∘
  ; assoc = assoc₂
  ; sym-assoc = sym-assoc₂
  ; identityˡ = identity₂ˡ
  ; identityʳ = identity₂ʳ
  ; identity² = identity₂²
  ; equiv = record
  -- must be delta expanded to type-check
  -- as functions are applied to different implicit parameters
    { refl = hom.Equiv.refl
    ; sym = hom.Equiv.sym
    ; trans = hom.Equiv.trans
    }
  ; ∘-resp-≈ = hom.∘-resp-≈
  }
  where
    open Bimodulehomomorphism using (α)
