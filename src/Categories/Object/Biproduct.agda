{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category

-- Biproducts, a-la Karvonen.
--
-- This definition has advantages over more traditional ones,
-- namely that that we don't require either enrichment in CMon/Ab, or Zero Objects.
--
-- See https://arxiv.org/abs/1801.06488
module Categories.Object.Biproduct {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Object.Coproduct 𝒞
open import Categories.Object.Product 𝒞

open import Categories.Morphism 𝒞

open Category 𝒞
open HomReasoning

private
  variable
    A B C D : Obj
    f g h : A ⇒ B

record IsBiproduct {A B A⊕B : Obj} (π₁ : A⊕B ⇒ A) (π₂ : A⊕B ⇒ B) (i₁ : A ⇒ A⊕B) (i₂ : B ⇒ A⊕B) : Set (o ⊔ ℓ ⊔ e) where
  field
    isCoproduct : IsCoproduct i₁ i₂
    isProduct : IsProduct π₁ π₂

    π₁∘i₁≈id : π₁ ∘ i₁ ≈ id
    π₂∘i₂≈id : π₂ ∘ i₂ ≈ id
    permute  : i₁ ∘ π₁ ∘ i₂ ∘ π₂ ≈ i₂ ∘ π₂ ∘ i₁ ∘ π₁

  open IsCoproduct isCoproduct public renaming (unique to []-unique)
  open IsProduct isProduct public renaming (unique to ⟨⟩-unique)

record Biproduct (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    A⊕B : Obj

    π₁    : A⊕B ⇒ A
    π₂    : A⊕B ⇒ B

    i₁    : A ⇒ A⊕B
    i₂    : B ⇒ A⊕B

    isBiproduct : IsBiproduct π₁ π₂ i₁ i₂

  open IsBiproduct isBiproduct public

IsBiproduct⇒Biproduct : {π₁ : C ⇒ A} {π₂ : C ⇒ B} {i₁ : A ⇒ C} {i₂ : B ⇒ C}  → IsBiproduct π₁ π₂ i₁ i₂ → Biproduct A B
IsBiproduct⇒Biproduct isBiproduct = record
  { isBiproduct = isBiproduct
  }

Biproduct⇒IsBiproduct : (b : Biproduct A B) → IsBiproduct (Biproduct.π₁ b) (Biproduct.π₂ b) (Biproduct.i₁ b) (Biproduct.i₂ b)
Biproduct⇒IsBiproduct biproduct = Biproduct.isBiproduct biproduct

Biproduct⇒Product : Biproduct A B → Product A B
Biproduct⇒Product b = record
  { ⟨_,_⟩ = ⟨_,_⟩
  ; project₁ = project₁
  ; project₂ = project₂
  ; unique = ⟨⟩-unique
  }
  where
    open Biproduct b

Biproduct⇒Coproduct : Biproduct A B → Coproduct A B
Biproduct⇒Coproduct b = record
  { [_,_] = [_,_]
  ; inject₁ = inject₁
  ; inject₂ = inject₂
  ; unique = []-unique
  }
  where
    open Biproduct b
