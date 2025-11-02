{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Bicategory
open import Categories.Bicategory.Monad using (Monad)

module Categories.Bicategory.Monad.Bimodule.Homomorphism {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {M₁ M₂ : Monad 𝒞} where

open import Level
open import Categories.Bicategory.Monad.Bimodule using (Bimodule)
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
import Categories.Morphism.Reasoning as MR

private
  module MR' {A B : Obj} where
    open MR (hom A B) public

record Bimodulehomomorphism (B₁ B₂ : Bimodule M₁ M₂) : Set (ℓ ⊔ e) where
  open Monad using (T)
  open Bimodule using (F; actionˡ; actionʳ)
  field
    α       : F B₁ ⇒₂ F B₂
    linearˡ : actionˡ B₂ ∘ᵥ (α ◁ T M₁) ≈ α ∘ᵥ actionˡ B₁
    linearʳ : actionʳ B₂ ∘ᵥ (T M₂ ▷ α) ≈ α ∘ᵥ actionʳ B₁

id-bimodule-hom : {B : Bimodule M₁ M₂} → Bimodulehomomorphism B B
id-bimodule-hom {B} = record
  { α = id₂
  ; linearˡ = id-linearˡ
  ; linearʳ = id-linearʳ
  }
  where
    open Monad using (C; T)
    open Bimodule B using (actionˡ; actionʳ)
    open hom.HomReasoning
    open MR'

    id-linearˡ : actionˡ ∘ᵥ (id₂ ◁ T M₁) ≈ id₂ ∘ᵥ actionˡ
    id-linearˡ = begin
      actionˡ ∘ᵥ (id₂ ◁ T M₁) ≈⟨ elimʳ ▷id₂ ⟩
      actionˡ                 ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ actionˡ          ∎

    id-linearʳ : actionʳ ∘ᵥ (T M₂ ▷ id₂) ≈ id₂ ∘ᵥ actionʳ
    id-linearʳ = begin
      actionʳ ∘ᵥ (T M₂ ▷ id₂) ≈⟨ elimʳ ▷id₂ ⟩
      actionʳ                 ≈⟨ ⟺ identity₂ˡ ⟩
      id₂ ∘ᵥ actionʳ          ∎

bimodule-hom-∘ : {B₁ B₂ B₃ : Bimodule M₁ M₂}
               → Bimodulehomomorphism B₂ B₃ → Bimodulehomomorphism B₁ B₂ → Bimodulehomomorphism B₁ B₃
bimodule-hom-∘ {B₁} {B₂} {B₃} g f = record
  { α = α g ∘ᵥ α f
  ; linearˡ = g∘f-linearˡ
  ; linearʳ = g∘f-linearʳ
  }
  where
    open Monad using (C; T)
    open Bimodule using (F; actionˡ; actionʳ)
    open Bimodulehomomorphism using (α; linearˡ; linearʳ)
    open hom.HomReasoning
    open MR'

    g∘f-linearˡ : actionˡ B₃ ∘ᵥ (α g ∘ᵥ α f) ◁ T M₁ ≈ (α g ∘ᵥ α f) ∘ᵥ actionˡ B₁
    g∘f-linearˡ = begin
      actionˡ B₃ ∘ᵥ (α g ∘ᵥ α f) ◁ T M₁            ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
      actionˡ B₃ ∘ᵥ (α g ◁ T M₁) ∘ᵥ (α f ◁ T M₁)   ≈⟨ glue′ (linearˡ g) (linearˡ f) ⟩
      (α g ∘ᵥ α f) ∘ᵥ actionˡ B₁                   ∎

    g∘f-linearʳ : actionʳ B₃ ∘ᵥ T M₂ ▷ (α g ∘ᵥ α f) ≈ (α g ∘ᵥ α f) ∘ᵥ actionʳ B₁
    g∘f-linearʳ = begin
      actionʳ B₃ ∘ᵥ T M₂ ▷ (α g ∘ᵥ α f)            ≈⟨ refl⟩∘⟨ (⟺ ∘ᵥ-distr-▷) ⟩
      actionʳ B₃ ∘ᵥ (T M₂ ▷ α g) ∘ᵥ (T M₂ ▷ α f)   ≈⟨ glue′ (linearʳ g) (linearʳ f) ⟩
      (α g ∘ᵥ α f) ∘ᵥ actionʳ B₁                   ∎
