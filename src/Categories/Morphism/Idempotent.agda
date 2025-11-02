{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category.Core

-- Idempotents and Split Idempotents
module Categories.Morphism.Idempotent {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning

record Idempotent (A : Obj) : Set (ℓ ⊔ e) where
  field
    idem       : A ⇒ A
    idempotent : idem ∘ idem ≈ idem

record IsSplitIdempotent {A : Obj} (i : A ⇒ A) : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj}    : Obj
    retract  : A ⇒ obj
    section  : obj ⇒ A
    retracts : retract ∘ section ≈ id
    splits   : section ∘ retract ≈ i

  retract-absorb : retract ∘ i ≈ retract
  retract-absorb = begin
    retract ∘ i                 ≈˘⟨ refl⟩∘⟨ splits ⟩
    retract ∘ section ∘ retract ≈⟨ cancelˡ retracts ⟩
    retract                     ∎

  section-absorb : i ∘ section ≈ section
  section-absorb = begin
    i ∘ section                   ≈˘⟨ splits ⟩∘⟨refl ⟩
    (section ∘ retract) ∘ section ≈⟨ cancelʳ retracts ⟩
    section                       ∎

  idempotent : i ∘ i ≈ i
  idempotent = begin
    i ∘ i                                     ≈˘⟨ splits ⟩∘⟨ splits ⟩
    (section ∘ retract) ∘ (section ∘ retract) ≈⟨ cancelInner retracts ⟩
    section ∘ retract                         ≈⟨ splits ⟩
    i                                         ∎

record SplitIdempotent (A : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    idem : A ⇒ A
    isSplitIdempotent : IsSplitIdempotent idem

  open IsSplitIdempotent isSplitIdempotent public

-- All split idempotents are idempotent
SplitIdempotent⇒Idempotent : ∀ {A} → SplitIdempotent A → Idempotent A
SplitIdempotent⇒Idempotent Split = record { Split }
  where
    module Split = SplitIdempotent Split

module _ {A} {f : A ⇒ A} (S T : IsSplitIdempotent f) where
  private
    module S = IsSplitIdempotent S
    module T = IsSplitIdempotent T

  split-idempotent-unique : S.obj ≅ T.obj
  split-idempotent-unique = record
    { from = T.retract ∘ S.section
    ; to = S.retract ∘ T.section
    ; iso = record
      { isoˡ = begin
        (S.retract ∘ T.section) ∘ (T.retract ∘ S.section) ≈⟨ center T.splits ⟩
        S.retract ∘ f ∘ S.section                         ≈⟨ pullˡ S.retract-absorb ⟩
        S.retract ∘ S.section                             ≈⟨ S.retracts ⟩
        id                                                ∎
      ; isoʳ = begin
        (T.retract ∘ S.section) ∘ (S.retract ∘ T.section) ≈⟨ center S.splits ⟩
        T.retract ∘ f ∘ T.section                         ≈⟨ pullˡ T.retract-absorb ⟩
        T.retract ∘ T.section                             ≈⟨ T.retracts ⟩
        id                                                ∎
      }
    }
