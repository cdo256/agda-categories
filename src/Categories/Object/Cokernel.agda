{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category
open import Categories.Object.Zero

-- Cokernels of morphisms.
-- https://ncatlab.org/nlab/show/cokernel
module Categories.Object.Cokernel {o ℓ e} {𝒞 : Category o ℓ e} (𝟎 : Zero 𝒞) where

open import Level

open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞
  hiding (glue)

open Category 𝒞
open Zero 𝟎

open HomReasoning

private
  variable
    A B X : Obj
    f h i j k : A ⇒ B

record IsCokernel {A B K} (f : A ⇒ B) (k : B ⇒ K) : Set (o ⊔ ℓ ⊔ e) where
  field
    commute   : k ∘ f ≈ zero⇒
    universal : ∀ {X} {h : B ⇒ X} → h ∘ f ≈ zero⇒ → K ⇒ X
    factors   : ∀ {eq : h ∘ f ≈ zero⇒} → h ≈ universal eq ∘ k
    unique    : ∀ {eq : h ∘ f ≈ zero⇒} → h ≈ i ∘ k → i ≈ universal eq

  universal-resp-≈ : ∀ {eq : h ∘ f ≈ zero⇒} {eq′ : i ∘ f ≈ zero⇒} →
    h ≈ i → universal eq ≈ universal eq′
  universal-resp-≈ h≈i = unique (⟺ h≈i ○ factors)

  universal-∘ : h ∘ k ∘ f ≈ zero⇒
  universal-∘ {h = h} = begin
    h ∘ k ∘ f ≈⟨ refl⟩∘⟨ commute ⟩
    h ∘ zero⇒ ≈⟨ zero-∘ˡ h ⟩
    zero⇒     ∎

record Cokernel {A B} (f : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    {cokernel} : Obj
    cokernel⇒  : B ⇒ cokernel
    isCokernel : IsCokernel f cokernel⇒

  open IsCokernel isCokernel public

IsCokernel⇒Cokernel : IsCokernel f k → Cokernel f
IsCokernel⇒Cokernel {k = k} isCokernel = record
  { cokernel⇒ = k
  ; isCokernel = isCokernel
  }
