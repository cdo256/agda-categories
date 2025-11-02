{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Diagram.Coequalizer {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning
open Equiv

open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open import Level
open import Function using (_$_)

private
  variable
    A B C : Obj
    h i j k : A ⇒ B

record IsCoequalizer {E} (f g : A ⇒ B) (arr : B ⇒ E) : Set (o ⊔ ℓ ⊔ e) where
  field
    equality   : arr ∘ f ≈ arr ∘ g
    coequalize : {h : B ⇒ C} → h ∘ f ≈ h ∘ g → E ⇒ C
    universal  : {h : B ⇒ C} {eq : h ∘ f ≈ h ∘ g} → h ≈ coequalize eq ∘ arr
    unique     : {h : B ⇒ C} {i : E ⇒ C} {eq : h ∘ f ≈ h ∘ g} → h ≈ i ∘ arr → i ≈ coequalize eq

  unique′ : (eq eq′ : h ∘ f ≈ h ∘ g) → coequalize eq ≈ coequalize eq′
  unique′ eq eq′ = unique universal

  id-coequalize : id ≈ coequalize equality
  id-coequalize = unique (⟺ identityˡ)

  coequalize-resp-≈ : ∀ {eq :  h ∘ f ≈ h ∘ g} {eq′ : i ∘ f ≈ i ∘ g} →
    h ≈ i → coequalize eq ≈ coequalize eq′
  coequalize-resp-≈ {h = h} {i = i} {eq = eq} {eq′ = eq′} h≈i = unique $ begin
    i                   ≈˘⟨ h≈i ⟩
    h                   ≈⟨ universal ⟩
    coequalize eq ∘ arr ∎

  coequalize-resp-≈′ : (eq :  h ∘ f ≈ h ∘ g) → (eq′ : i ∘ f ≈ i ∘ g) →
    h ≈ i → j ≈ coequalize eq → k ≈ coequalize eq′ → j ≈ k
  coequalize-resp-≈′ {j = j} {k = k} eq eq′ h≈i eqj eqk = begin
    j              ≈⟨ eqj ⟩
    coequalize eq  ≈⟨ coequalize-resp-≈ h≈i ⟩
    coequalize eq′ ≈˘⟨ eqk ⟩
    k              ∎

-- This could be proved via duality, but is easier to just write by hand,
-- as it makes the dependency graph a lot cleaner.
IsCoequalizer⇒Epi : IsCoequalizer h i j → Epi j
IsCoequalizer⇒Epi coeq _ _ eq =
  coequalize-resp-≈′ (extendˡ equality) (extendˡ equality) eq (unique refl) (unique refl)
  where
    open IsCoequalizer coeq

record Coequalizer (f g : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : Obj
    arr   : B ⇒ obj
    isCoequalizer : IsCoequalizer f g arr

  open IsCoequalizer isCoequalizer public

Coequalizer⇒Epi : (e : Coequalizer h i) → Epi (Coequalizer.arr e)
Coequalizer⇒Epi coeq = IsCoequalizer⇒Epi isCoequalizer
  where
    open Coequalizer coeq

-- Proving this via duality arguments is kind of annoying, as ≅ does not behave nicely in
-- concert with op.
up-to-iso : (coe₁ coe₂ : Coequalizer h i) → Coequalizer.obj coe₁ ≅ Coequalizer.obj coe₂
up-to-iso coe₁ coe₂ = record
  { from = repack coe₁ coe₂
  ; to = repack coe₂ coe₁
  ; iso = record
    { isoˡ = repack-cancel coe₂ coe₁
    ; isoʳ = repack-cancel coe₁ coe₂
    }
  }
  where
    open Coequalizer

    repack : (coe₁ coe₂ : Coequalizer h i) → obj coe₁ ⇒ obj coe₂
    repack coe₁ coe₂ = coequalize coe₁ (equality coe₂)

    repack∘ : (coe₁ coe₂ coe₃ : Coequalizer h i) → repack coe₂ coe₃ ∘ repack coe₁ coe₂ ≈ repack coe₁ coe₃
    repack∘ coe₁ coe₂ coe₃ = unique coe₁ (⟺ (glueTrianglesˡ (⟺ (universal coe₂)) (⟺ (universal coe₁)))) -- unique e₃ (⟺ (glueTrianglesʳ (⟺ (universal e₃)) (⟺ (universal e₂))))

    repack-cancel : (e₁ e₂ : Coequalizer h i) → repack e₁ e₂ ∘ repack e₂ e₁ ≈ id
    repack-cancel coe₁ coe₂ = repack∘ coe₂ coe₁ coe₂ ○ ⟺ (id-coequalize coe₂)

-- We prove that the isomorphism of up-to-iso fits into a triangle --
up-to-iso-triangle : (coe₁ coe₂ : Coequalizer h i) →
                     _≅_.from (up-to-iso coe₁ coe₂) ∘ Coequalizer.arr coe₁
                     ≈ Coequalizer.arr coe₂
up-to-iso-triangle coe₁ coe₂ = ⟺ (Coequalizer.universal coe₁)

IsCoequalizer⇒Coequalizer : IsCoequalizer h i k → Coequalizer h i
IsCoequalizer⇒Coequalizer {k = k} is-coe = record
  { arr = k
  ; isCoequalizer = is-coe
  }

Coequalizers : Set (o ⊔ ℓ ⊔ e)
Coequalizers = {A B : Obj} → (f g : A ⇒ B) → Coequalizer f g
