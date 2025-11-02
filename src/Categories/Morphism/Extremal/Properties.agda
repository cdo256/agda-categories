{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category.Core

module Categories.Morphism.Extremal.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (_$_)

open import Categories.Diagram.Equalizer 𝒞
open import Categories.Diagram.Coequalizer 𝒞

open import Categories.Morphism 𝒞
open import Categories.Morphism.Extremal 𝒞
open import Categories.Morphism.Properties 𝒞
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Morphism.Regular 𝒞

open Category 𝒞
open HomReasoning

private
  variable
    A B : Obj
    f g : A ⇒ B

--------------------------------------------------------------------------------
-- Extremal Epimorphisms

RegularEpi⇒IsExtremalEpi : ∀ {A B} {f : A ⇒ B} (e : RegularEpi f) → IsExtremalEpi (RegularEpi⇒Epi e)
RegularEpi⇒IsExtremalEpi {A = A} {B = B} {f = f} regular {X = X} {i = i} {g = k} i-mono f≈i∘k =
  record
    { inv = i⁻¹
    ; iso = record
      { isoˡ = isoˡ
      ; isoʳ = isoʳ
      }
    }
  where
    open RegularEpi regular renaming (g to r; h to s)
    open IsCoequalizer coequalizer

    i⁻¹ : B ⇒ X
    i⁻¹ = coequalize $ i-mono (k ∘ s) (k ∘ r) $ begin
        i ∘ k ∘ s ≈⟨ pullˡ (⟺ f≈i∘k) ⟩
        f ∘ s     ≈⟨ equality ⟩
        f ∘ r     ≈⟨ pushˡ f≈i∘k ⟩
        i ∘ k ∘ r ∎

    isoʳ : i ∘ i⁻¹ ≈ id
    isoʳ = RegularEpi⇒Epi regular (i ∘ i⁻¹) id $ begin
      (i ∘ i⁻¹) ∘ f ≈⟨ pullʳ (⟺ universal) ⟩
      i ∘ k         ≈˘⟨ f≈i∘k ⟩
      f             ≈˘⟨ identityˡ ⟩
      id ∘ f        ∎

    isoˡ : i⁻¹ ∘ i ≈ id
    isoˡ = i-mono (i⁻¹ ∘ i) id $ begin
      i ∘ i⁻¹ ∘ i ≈⟨ cancelˡ isoʳ ⟩
      i           ≈˘⟨ identityʳ ⟩
      i ∘ id      ∎

RegularEpi⇒ExtremalEpi : (e : RegularEpi f) → ExtremalEpi f
RegularEpi⇒ExtremalEpi e = record
  { epi = RegularEpi⇒Epi e
  ; extremal = RegularEpi⇒IsExtremalEpi e
  }

ExtremalEpi-∘₂ : ExtremalEpi (f ∘ g) → ExtremalEpi f
ExtremalEpi-∘₂ fg-extremal = record
  { epi = Epi-∘₂ epi
  ; extremal = λ i-mono eq → extremal i-mono (pushˡ eq)
  }
  where
    open ExtremalEpi fg-extremal

ExtremalEpi-∘ : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → ExtremalEpi f → RegularEpi g → ExtremalEpi (f ∘ g)
ExtremalEpi-∘ {A = A} {B = B} {C = C} {f = f} {g = g} f-extremal g-regular = record
  { epi = fg-epi
  ; extremal = fg-extremal
  }
  where
    module f-extremal = ExtremalEpi f-extremal
    module g-regular = RegularEpi g-regular
    open IsCoequalizer g-regular.coequalizer

    g-epi : Epi g
    g-epi = RegularEpi⇒Epi g-regular

    fg-epi : Epi (f ∘ g)
    fg-epi = Epi-∘ f-extremal.epi g-epi

    fg-extremal : IsExtremalEpi fg-epi
    fg-extremal {X = X} {i = i} {g = h} i-mono f∘g≈i∘h =
      f-extremal.extremal i-mono $ g-epi _ _ $ begin
        f ∘ g       ≈⟨ f∘g≈i∘h ⟩
        i ∘ h       ≈⟨ pushʳ universal ⟩
        (i ∘ k) ∘ g ∎
      where
        k : B ⇒ X
        k = coequalize $ i-mono _ _ $ begin
          i ∘ h ∘ g-regular.h ≈⟨ extendʳ (⟺ f∘g≈i∘h) ⟩
          f ∘ g ∘ g-regular.h ≈⟨ refl⟩∘⟨ equality ⟩
          f ∘ g ∘ g-regular.g ≈⟨ extendʳ f∘g≈i∘h ⟩
          i ∘ h ∘ g-regular.g ∎

ExtremalEpi+Mono⇒IsIso : ExtremalEpi f → Mono f → IsIso f
ExtremalEpi+Mono⇒IsIso {f = f} f-extremal f-mono = extremal f-mono (⟺ identityʳ)
  where
    open ExtremalEpi f-extremal

--------------------------------------------------------------------------------
-- Extremal Monomorphisms

RegularMono⇒IsExtremalMono : ∀ {A B} {f : A ⇒ B} (m : RegularMono f) → IsExtremalMono (RegularMono⇒Mono m)
RegularMono⇒IsExtremalMono {A = A} {B = B} {f = f} regular {X = X} {g = k} {i = i} i-epi f≈k∘i =
  record
    { inv = i⁻¹
    ; iso = record
      { isoˡ = isoˡ
      ; isoʳ = isoʳ
      }
    }
    where
      open RegularMono regular renaming (g to r; h to s)
      open IsEqualizer equalizer

      i⁻¹ : X ⇒ A
      i⁻¹ = equalize $ i-epi (s ∘ k) (r ∘ k) $ begin
        (s ∘ k) ∘ i ≈⟨ pullʳ (⟺ f≈k∘i) ⟩
        s ∘ f       ≈⟨ equality ⟩
        r ∘ f       ≈⟨ pushʳ f≈k∘i ⟩
        (r ∘ k) ∘ i ∎

      isoˡ : i⁻¹ ∘ i ≈ id
      isoˡ = RegularMono⇒Mono regular (i⁻¹ ∘ i) id $ begin
        f ∘ i⁻¹ ∘ i ≈⟨ pullˡ (⟺ universal) ⟩
        k ∘ i       ≈˘⟨ f≈k∘i ⟩
        f           ≈˘⟨ identityʳ ⟩
        f ∘ id      ∎

      isoʳ : i ∘ i⁻¹ ≈ id
      isoʳ = i-epi (i ∘ i⁻¹) id $ begin
        (i ∘ i⁻¹) ∘ i ≈⟨ cancelʳ isoˡ ⟩
        i             ≈˘⟨ identityˡ ⟩
        id ∘ i        ∎

RegularMono⇒ExtremalMono : RegularMono f → ExtremalMono f
RegularMono⇒ExtremalMono m = record
  { mono = RegularMono⇒Mono m
  ; extremal = RegularMono⇒IsExtremalMono m
  }

ExtremalMono-∘₂ : ExtremalMono (f ∘ g) → ExtremalMono g
ExtremalMono-∘₂ fg-extremal = record
  { mono = Mono-∘₂ mono
  ; extremal = λ i-epi eq → extremal i-epi (pushʳ eq)
  }
  where
    open ExtremalMono fg-extremal

ExtremalMono-∘ : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → RegularMono f → ExtremalMono g → ExtremalMono (f ∘ g)
ExtremalMono-∘ {A = A} {B = B} {f = f} {g = g} f-regular g-extremal = record
  { mono = fg-mono
  ; extremal = fg-extremal
  }
  where
    module f-regular = RegularMono f-regular
    open IsEqualizer f-regular.equalizer
    module g-extremal = ExtremalMono g-extremal

    f-mono : Mono f
    f-mono = (RegularMono⇒Mono f-regular)

    fg-mono : Mono (f ∘ g)
    fg-mono = Mono-∘ f-mono g-extremal.mono

    fg-extremal : IsExtremalMono fg-mono
    fg-extremal {X = X} {g = h} {i = e} e-epi f∘g≈h∘e =
      g-extremal.extremal e-epi $ f-mono _ _ $ begin
      f ∘ g     ≈⟨ f∘g≈h∘e ⟩
      h ∘ e     ≈⟨ pushˡ universal ⟩
      f ∘ k ∘ e ∎
      where
        k : X ⇒ B
        k = equalize $ e-epi _ _ $ begin
          (f-regular.h ∘ h) ∘ e ≈⟨ extendˡ (⟺ f∘g≈h∘e) ⟩
          (f-regular.h ∘ f) ∘ g ≈⟨ equality ⟩∘⟨refl ⟩
          (f-regular.g ∘ f) ∘ g ≈⟨ extendˡ f∘g≈h∘e ⟩
          (f-regular.g ∘ h) ∘ e ∎

ExtremalMono+Epi⇒IsIso : ExtremalMono f → Epi f → IsIso f
ExtremalMono+Epi⇒IsIso {f = f} f-extremal f-epi = extremal f-epi (⟺ identityˡ)
  where
    open ExtremalMono f-extremal

--------------------------------------------------------------------------------
-- Extremal Morphisms in Balanced Categories
-- https://ncatlab.org/nlab/show/balanced+category

module _ (balanced : ∀ {A B} {f : A ⇒ B} → Mono f → Epi f → IsIso f) where

  Mono+Epi⇒IsExtremalEpi : (e : Epi f) → IsExtremalEpi e
  Mono+Epi⇒IsExtremalEpi {f = f} f-epi {i = i} {g = g} i-mono f≈i∘g = balanced i-mono i-epi
    where
      i-epi : Epi i
      i-epi g₁ g₂ g₁∘i≈g₂∘i = f-epi g₁ g₂ $ begin
        g₁ ∘ f       ≈⟨ pushʳ f≈i∘g ⟩
        (g₁ ∘ i) ∘ g ≈⟨ g₁∘i≈g₂∘i ⟩∘⟨refl ⟩
        (g₂ ∘ i) ∘ g ≈⟨ pullʳ (⟺ f≈i∘g) ⟩
        g₂ ∘ f ∎

  Mono+Epi⇒IsExtremalMono : (m : Mono f) → IsExtremalMono m
  Mono+Epi⇒IsExtremalMono {f = f} f-mono {g = g} {i = i} i-epi f≈g∘i = balanced i-mono i-epi
    where
      i-mono : Mono i
      i-mono g₁ g₂ i∘g₁≈i∘g₂ = f-mono g₁ g₂ $ begin
        f ∘ g₁     ≈⟨ pushˡ f≈g∘i ⟩
        g ∘ i ∘ g₁ ≈⟨ refl⟩∘⟨ i∘g₁≈i∘g₂ ⟩
        g ∘ i ∘ g₂ ≈⟨ pullˡ (⟺ f≈g∘i) ⟩
        f ∘ g₂     ∎
