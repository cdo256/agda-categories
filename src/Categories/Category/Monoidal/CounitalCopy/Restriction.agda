{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.CounitalCopy using (CounitalCopy)
open import Categories.Category.Restriction using (Restriction)
open import Data.Product using (_,_)

import Categories.Morphism.Reasoning as MR
import Categories.Morphism as M

-- Counital copy categories admit a non trivial restriction structure.

module Categories.Category.Monoidal.CounitalCopy.Restriction {o ℓ e} {𝒞 : Category o ℓ e} {monoidal : Monoidal 𝒞} {symmetric : Symmetric monoidal} (counitalCopy : CounitalCopy symmetric) where
  open Category 𝒞
  open Symmetric symmetric
  open CounitalCopy counitalCopy
  open Equiv
  open M 𝒞
  open MR 𝒞
  open HomReasoning
  open import Categories.Category.Monoidal.Utilities monoidal
  open Shorthands
  open import Categories.Category.Monoidal.Properties monoidal
  open import Categories.Category.Monoidal.Braided.Properties braided using (braiding-coherence) renaming (module Shorthands to BraidedShorthands)
  open BraidedShorthands using (σ⇒)

  restriction : Restriction 𝒞
  restriction = record
    { _↓ = _↓
    ; pidʳ = pidʳ'
    ; ↓-comm = ↓-comm''
    ; ↓-denestʳ = ↓-denestʳ'
    ; ↓-skew-comm = ↓-skew-comm'
    ; ↓-cong = λ f≈g → refl⟩∘⟨ refl⟩∘⟨ ⊗.F-resp-≈ (f≈g , refl) ⟩∘⟨refl
    }
    where
      _↓ : ∀ {A B} → A ⇒ B → A ⇒ A
      _↓ {A} {B} f = λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ
      pidʳ' : ∀ {A B} {f : A ⇒ B} → f ∘ f ↓ ≈ f
      pidʳ' {f = f} = begin 
        f ∘ λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ         ≈⟨ extendʳ (sym unitorˡ-commute-from) ⟩ 
        λ⇒ ∘ (id ⊗₁ f) ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ ≈⟨ refl⟩∘⟨ (extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm-sym , id-comm) ○ ⊗.homomorphism)) ⟩ 
        λ⇒ ∘ (δ ⊗₁ id) ∘ (id ⊗₁ f) ∘ (f ⊗₁ id) ∘ Δ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ⟩ 
        λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ f) ∘ Δ              ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ natural f ⟩
        λ⇒ ∘ (δ ⊗₁ id) ∘ Δ ∘ f                     ≈⟨ refl⟩∘⟨ (pullˡ (sym δ-identityˡ)) ⟩ 
        λ⇒ ∘ λ⇐ ∘ f                                ≈⟨ cancelˡ unitorˡ.isoʳ ⟩ 
        f                                          ∎
      ↓-comm' : ∀ {A B C} (f : A ⇒ B) (g : A ⇒ C) → f ↓ ∘ g ↓ ≈ λ⇒ ∘ (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((g ⊗₁ f) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
      ↓-comm' f g = begin 
        (λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ) ∘ λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ
          ≈⟨ pullʳ (pullʳ (pullʳ (extendʳ (sym unitorˡ-commute-from)))) ⟩ 
        λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ λ⇒ ∘ (id ⊗₁ Δ) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm-sym , id-comm) ○ ⊗.homomorphism) ⟩
        λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ λ⇒ ∘ (δ ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ (g ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm-sym , id-comm) ○ ⊗.homomorphism) ⟩
        λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym unitorˡ-commute-from) ⟩
        λ⇒ ∘ (δ ⊗₁ id) ∘ λ⇒ ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
          ≈⟨ refl⟩∘⟨ extendʳ (sym unitorˡ-commute-from) ⟩
        λ⇒ ∘ λ⇒ ∘ (id ⊗₁ (δ ⊗₁ id)) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ helper ⟩
        λ⇒ ∘ λ⇒ ∘ (id ⊗₁ (δ ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ α⇒ ∘ ((id ⊗₁ f) ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ○ extendʳ (sym assoc-commute-from)) ⟩ 
        λ⇒ ∘ λ⇒ ∘ α⇒ ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) , identity²)) ⟩
        λ⇒ ∘ λ⇒ ∘ α⇒ ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((g ⊗₁ f) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ 
          ≈⟨ refl⟩∘⟨ (pullˡ coherence₁) ⟩
        λ⇒ ∘ (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((g ⊗₁ f) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ∎
          where
          helper : (id ⊗₁ (f ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ ≈ (δ ⊗₁ id) ∘ α⇒ ∘ ((id ⊗₁ f) ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          helper = begin 
            (id ⊗₁ (f ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
              ≈⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm-sym , id-comm) ○ ⊗.homomorphism) ⟩
            (δ ⊗₁ id) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (g ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
              ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoʳ ⟩
            (δ ⊗₁ id) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (g ⊗₁ id) ∘ α⇒ ∘ α⇐ ∘ (id ⊗₁ Δ) ∘ Δ
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ sym Δ-assoc) ⟩
            (δ ⊗₁ id) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (g ⊗₁ id) ∘ α⇒ ∘ (Δ ⊗₁ id) ∘ Δ
              ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (assoc-commute-from ○ ∘-resp-≈ˡ (⊗.F-resp-≈ (refl , ⊗.identity))) ⟩
            (δ ⊗₁ id) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ α⇒ ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
              ≈⟨ refl⟩∘⟨ extendʳ (sym assoc-commute-from) ⟩
            (δ ⊗₁ id) ∘ α⇒ ∘ ((id ⊗₁ f) ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
              ∎
      ↓-comm'' : ∀ {A B C} {f : A ⇒ B} {g : A ⇒ C} → f ↓ ∘ g ↓ ≈ g ↓ ∘ f ↓
      ↓-comm'' {f = f} {g} = begin 
        (λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ) ∘ λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ
          ≈⟨ ↓-comm' f g ⟩
        λ⇒ ∘ (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((g ⊗₁ f) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (cocommutative , identity²)) ⟩
        λ⇒ ∘ (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((g ⊗₁ f) ⊗₁ id) ∘ (σ⇒ ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((sym (braiding.⇒.commute _)) , refl) ○ ⊗.homomorphism) ⟩
        λ⇒ ∘ (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ (σ⇒ ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((sym (braiding.⇒.commute _)) , refl) ○ ⊗.homomorphism) ⟩
        λ⇒ ∘ (λ⇒ ⊗₁ id) ∘ (σ⇒ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ (pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((braiding-coherence ○ sym coherence₃) , identity²))) ⟩
        λ⇒ ∘ (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈˘⟨ ↓-comm' g f ⟩
        (λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ) ∘ λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ 
          ∎
      ↓-denestʳ' : ∀ {A B C} {f : A ⇒ B} {g : A ⇒ C} → (g ∘ f ↓) ↓ ≈ g ↓ ∘ f ↓
      ↓-denestʳ' {f = f} {g} = begin
        λ⇒ ∘ (δ ⊗₁ id) ∘ ((g ∘ λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ) ⊗₁ id) ∘ Δ
          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ∘-resp-≈ˡ (⊗.F-resp-≈ ((assoc ○ assoc ○ assoc) , elimˡ (elimˡ (elimˡ identity²)))) ⟩
        λ⇒ ∘ (δ ⊗₁ id) ∘ (((((g ∘ λ⇒) ∘ (δ ⊗₁ id)) ∘ (f ⊗₁ id)) ∘ Δ) ⊗₁ ((((id ∘ id) ∘ id) ∘ id) ∘ id)) ∘ Δ
          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ (sym ⊗.homomorphism) ○ pullˡ (sym ⊗.homomorphism) ○ pullˡ (sym ⊗.homomorphism) ○ pullˡ (sym ⊗.homomorphism)) ⟩
        λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ id) ⊗₁ id) ∘ ((f ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ helper ⟩ 
        λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ λ⇒ ∘ (id ⊗₁ Δ) ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ
          ≈˘⟨ pullʳ (pullʳ (pullʳ (extendʳ (sym unitorˡ-commute-from)))) ⟩ 
        (λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ) ∘ λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ 
          ∎
          where
          helper : (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ id) ⊗₁ id) ∘ ((f ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ ≈ λ⇒ ∘ (id ⊗₁ Δ) ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ
          helper = begin 
            (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ id) ⊗₁ id) ∘ ((f ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
              ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ sym Δ-assoc) ⟩ 
            (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ id) ⊗₁ id) ∘ ((f ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ Δ) ∘ Δ
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym assoc-commute-to ○ ∘-resp-≈ʳ (⊗.F-resp-≈ (refl , ⊗.identity))) ⟩ 
            (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ (f ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
              ≈⟨ refl⟩∘⟨ extendʳ (sym assoc-commute-to ○ ∘-resp-≈ʳ (⊗.F-resp-≈ (refl , ⊗.identity))) ⟩ 
            (λ⇒ ⊗₁ id) ∘ α⇐ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
              ≈˘⟨ pullˡ coherence₁ ⟩ 
            λ⇒ ∘ α⇒ ∘ α⇐ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
              ≈⟨ refl⟩∘⟨ cancelˡ associator.isoʳ ⟩
            λ⇒ ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm , id-comm-sym) ○ ⊗.homomorphism) ⟩ 
            λ⇒ ∘ (δ ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ (f ⊗₁ id) ∘ Δ
              ≈⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm , id-comm-sym) ○ ⊗.homomorphism) ⟩ 
            λ⇒ ∘ (id ⊗₁ Δ) ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ 
              ∎
      ↓-skew-comm' : ∀ {A B C} {f : A ⇒ B} {g : B ⇒ C} → g ↓ ∘ f ≈ f ∘ (g ∘ f) ↓
      ↓-skew-comm' {f = f} {g} = begin 
        (λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ) ∘ f                   
          ≈⟨ pullʳ (pullʳ (pullʳ (natural f))) ⟩ 
        λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (f ⊗₁ f) ∘ Δ              
          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ⟩ 
        λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ f) ∘ (f ⊗₁ id) ∘ Δ 
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm , id-comm-sym) ○ ⊗.homomorphism)) ⟩ 
        λ⇒ ∘ (δ ⊗₁ id) ∘ (id ⊗₁ f) ∘ (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ 
          ≈⟨ refl⟩∘⟨ (extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm , id-comm-sym) ○ ⊗.homomorphism)) ⟩  
        λ⇒ ∘ (id ⊗₁ f) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ 
          ≈⟨ extendʳ unitorˡ-commute-from ⟩ 
        f ∘ λ⇒ ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ         
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identity²)) ⟩ 
        f ∘ λ⇒ ∘ (δ ⊗₁ id) ∘ ((g ∘ f) ⊗₁ id) ∘ Δ               
          ∎
