{-# OPTIONS --cubical-compatible --without-K --safe #-}

-- Mentioned in passing here:
-- https://ncatlab.org/nlab/show/slice+2-category

open import Categories.Bicategory using (Bicategory)

module Categories.Bicategory.Construction.LaxSlice
       {o ℓ e t}
       (𝒞 : Bicategory o ℓ e t)
       where

open import Data.Product using (_,_)
open import Function using (_$_)
open import Level using (_⊔_)

open import Categories.Bicategory.Extras 𝒞
open Shorthands
open import Categories.Category using () renaming (Category to 1Category)
open import Categories.Functor using (Functor)
open Functor using (F₀)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Construction.Constant using (const)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper)

record SliceObj (X : Obj) : Set (t ⊔ o) where
  constructor sliceobj
  field
    {Y} : Obj
    arr : Y ⇒₁ X

module SliceHom (A : Obj) where

  record Slice⇒₁ (X Y : SliceObj A) : Set (o ⊔ ℓ) where
    constructor slicearr₁
    private
      module X = SliceObj X
      module Y = SliceObj Y

    field
      {h} : X.Y ⇒₁ Y.Y
      Δ   : X.arr ⇒₂ (Y.arr ∘₁ h)

  record Slice⇒₂ {X Y : SliceObj A} (J K : Slice⇒₁ X Y) : Set (ℓ ⊔ e) where
    constructor slicearr₂
    private
      module Y = SliceObj Y
      module J = Slice⇒₁ J
      module K = Slice⇒₁ K

    field
      {ϕ} : J.h ⇒₂ K.h
      E   : K.Δ ≈ (Y.arr ▷ ϕ ∘ᵥ J.Δ)

  _∘ᵥ/_ : ∀ {X Y : SliceObj A}{J K L : Slice⇒₁ X Y} → Slice⇒₂ K L → Slice⇒₂ J K → Slice⇒₂ J L
  _∘ᵥ/_ {X}{Y}{J}{K}{L} (slicearr₂ {ϕ = ϕ} E) (slicearr₂ {ϕ = ψ} F) = slicearr₂ {ϕ = ϕ ∘ᵥ ψ} $ begin
      L.Δ                             ≈⟨ E ⟩
      (Y.arr ▷ ϕ ∘ᵥ K.Δ)              ≈⟨ refl⟩∘⟨ F ⟩
      Y.arr ▷ ϕ ∘ᵥ (Y.arr ▷ ψ ∘ᵥ J.Δ) ≈⟨ pullˡ ∘ᵥ-distr-▷ ⟩
      Y.arr ▷ (ϕ ∘ᵥ ψ) ∘ᵥ J.Δ         ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module J = Slice⇒₁ J
          module K = Slice⇒₁ K
          module L = Slice⇒₁ L
          open 1Category (hom X.Y A)
          open HomReasoning
          open Equiv
          open MR (hom X.Y A)

  SliceHomCat : SliceObj A → SliceObj A → 1Category (o ⊔ ℓ) (ℓ ⊔ e) e
  SliceHomCat X Y = record
    { Obj = Slice⇒₁ X Y
    ; _⇒_ = Slice⇒₂
    ; _≈_ = λ (slicearr₂ {ϕ} _) (slicearr₂ {ψ} _) → ϕ ≈ ψ
    ; id = slice-id _
    ; _∘_ = _∘ᵥ/_
    ; assoc = hom.assoc
    ; sym-assoc = hom.sym-assoc
    ; identityˡ = hom.identityˡ
    ; identityʳ = hom.identityʳ
    ; identity² = hom.identity²
    ; equiv = record { refl = refl ; sym = sym ; trans = trans }
    ; ∘-resp-≈ = hom.∘-resp-≈
    }
    where
      open hom.Equiv
      module X = SliceObj X
      module Y = SliceObj Y

      slice-id : ∀ (J : Slice⇒₁ X Y) → Slice⇒₂ J J
      slice-id J = slicearr₂ $ begin
        J.Δ                 ≈˘⟨ identity₂ˡ ⟩
        id₂ ∘ᵥ J.Δ          ≈˘⟨ ▷id₂ ⟩∘⟨refl ⟩
        (Y.arr ▷ id₂) ∘ J.Δ ∎
        where module J = Slice⇒₁ J
              open 1Category (hom X.Y A)
              open HomReasoning

  _⊚₀/_ : ∀ {X Y Z : SliceObj A} → Slice⇒₁ Y Z → Slice⇒₁ X Y → Slice⇒₁ X Z
  _⊚₀/_ {X}{Y}{Z} J K = slicearr₁ ((α⇒ ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ)
    where module K = Slice⇒₁ K
          module J = Slice⇒₁ J

  _⊚₁/_ : ∀ {X Y Z : SliceObj A} → {J J' : Slice⇒₁ Y Z} → {K K' : Slice⇒₁ X Y} → Slice⇒₂ J J' → Slice⇒₂ K K' → Slice⇒₂ (J ⊚₀/ K) (J' ⊚₀/ K')
  _⊚₁/_ {X}{Y}{Z}{J'}{J}{K'}{K} δ γ = slicearr₂ $ begin
    (α⇒ ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ                                                  ≈⟨ (refl⟩∘⟨ γ.E) ⟩
    (α⇒ ∘ᵥ J.Δ ◁ K.h) ∘ᵥ (Y.arr ▷ γ.ϕ ∘ᵥ K'.Δ)                                ≈⟨ ((refl⟩∘⟨ δ.E ⟩⊚⟨refl) ⟩∘⟨refl) ⟩
    (α⇒ ∘ᵥ (Z.arr ▷ δ.ϕ ∘ᵥ J'.Δ) ◁ K.h) ∘ᵥ (Y.arr ▷ γ.ϕ ∘ᵥ K'.Δ)              ≈˘⟨ (((refl⟩∘⟨ ∘ᵥ-distr-◁ ) ⟩∘⟨refl)) ⟩
    (α⇒ ∘ᵥ ((Z.arr ▷ δ.ϕ) ◁ K.h ∘ᵥ J'.Δ ◁ K.h)) ∘ᵥ (Y.arr ▷ γ.ϕ ∘ᵥ K'.Δ)      ≈⟨ pullʳ (center (sym ◁-▷-exchg)) ⟩
    α⇒ ∘ᵥ (Z.arr ▷ δ.ϕ) ◁ K.h ∘ᵥ (Z.arr ⊚₀ J'.h ▷ γ.ϕ ∘ᵥ J'.Δ ◁ K'.h) ∘ᵥ K'.Δ ≈⟨ pushʳ ( pullˡ (pullˡ (sym ⊚.homomorphism)) ) ⟩
    (α⇒ ∘ᵥ (Z.arr ▷ δ.ϕ ∘ᵥ id₂) ⊚₁ (id₂ ∘ᵥ γ.ϕ) ∘ᵥ J'.Δ ◁ K'.h) ∘ᵥ K'.Δ       ≈⟨ ((refl⟩∘⟨ (identity₂ʳ ⟩⊚⟨ identity₂ˡ ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
    (α⇒ ∘ᵥ ((Z.arr ▷ δ.ϕ) ⊚₁ γ.ϕ) ∘ᵥ J'.Δ ◁ K'.h) ∘ᵥ K'.Δ                     ≈⟨ pushˡ (pullˡ (⊚-assoc.⇒.commute ((id₂ , δ.ϕ) , γ.ϕ))) ⟩
    (Z.arr ▷ δ.ϕ ⊚₁ γ.ϕ ∘ᵥ α⇒) ∘ᵥ J'.Δ ◁ K'.h ∘ᵥ K'.Δ                         ≈⟨ pullʳ (sym assoc) ⟩
    (Z.arr ▷ δ.ϕ ⊚₁ γ.ϕ) ∘ᵥ ((α⇒ ∘ᵥ J'.Δ ◁ K'.h) ∘ᵥ K'.Δ)                     ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module Z = SliceObj Z
          module J = Slice⇒₁ J
          module J' = Slice⇒₁ J'
          module K = Slice⇒₁ K
          module K' = Slice⇒₁ K'
          module γ = Slice⇒₂ γ
          module δ = Slice⇒₂ δ
          open 1Category (hom X.Y A)
          open HomReasoning
          open MR (hom X.Y A)
          open Equiv

  id/ : ∀ {X : SliceObj A} → Slice⇒₁ X X
  id/ = slicearr₁ ρ⇐

  _⊚/_ : ∀ {X Y Z : SliceObj A} → Bifunctor (SliceHomCat Y Z) (SliceHomCat X Y) (SliceHomCat X Z)
  _⊚/_ {X}{Y}{Z} = record
    { F₀ = λ (J , K) → J ⊚₀/ K
    ; F₁ = λ (δ , γ) → δ ⊚₁/ γ
      ; identity = ⊚.identity
      ; homomorphism = ⊚.homomorphism
      ; F-resp-≈ = ⊚.F-resp-≈
      }
      where module X = SliceObj X
            module Y = SliceObj Y
            module Z = SliceObj Z

  α⇒/ : ∀ {W X Y Z}(J : Slice⇒₁ Y Z) (K : Slice⇒₁ X Y) (L : Slice⇒₁ W X) → Slice⇒₂ ((J ⊚₀/ K) ⊚₀/ L) (J ⊚₀/ (K ⊚₀/ L))
  α⇒/ {W}{X}{Y}{Z} J K L = slicearr₂ $ begin
    (α⇒ ∘ᵥ J.Δ ◁ K.h ⊚₀ L.h) ∘ᵥ ((α⇒ ∘ᵥ K.Δ ◁ L.h) ∘ᵥ L.Δ  )                  ≈⟨ pullʳ (center⁻¹ (sym α⇒-◁-∘₁) refl) ⟩
    α⇒ ∘ᵥ (α⇒ ∘ᵥ J.Δ ◁ K.h ◁ L.h) ∘ᵥ K.Δ ◁ L.h ∘ᵥ L.Δ                         ≈⟨ pullˡ (pullˡ (sym pentagon)) ⟩
    ((Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ L.h) ∘ᵥ J.Δ ◁ K.h ◁ L.h) ∘ᵥ (K.Δ ◁ L.h ∘ᵥ L.Δ) ≈⟨ pullˡ (pushˡ (pull-last ∘ᵥ-distr-◁ )) ⟩
    (Z.arr ▷ α⇒ ∘ᵥ (α⇒ ∘ᵥ ((α⇒ ∘ᵥ J.Δ ◁ K.h) ◁ L.h)) ∘ᵥ K.Δ ◁ L.h) ∘ᵥ L.Δ     ≈⟨ pushˡ (pushʳ (pullʳ ∘ᵥ-distr-◁)) ⟩
    ((Z.arr ▷ α⇒ ∘ᵥ α⇒)) ∘ᵥ (((α⇒ ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ) ◁ L.h) ∘ᵥ L.Δ         ≈⟨ pullʳ (pushʳ refl) ⟩
    Z.arr ▷ α⇒ ∘ᵥ ((α⇒ ∘ᵥ (((α⇒ ∘ᵥ J.Δ ◁ K.h)) ∘ᵥ K.Δ) ◁ L.h) ∘ᵥ L.Δ)         ∎
    where module W = SliceObj W
          module X = SliceObj X
          module Y = SliceObj Y
          module Z = SliceObj Z
          module J = Slice⇒₁ J
          module K = Slice⇒₁ K
          module L = Slice⇒₁ L
          open 1Category (hom W.Y A)
          open HomReasoning
          open MR (hom W.Y A)
          open hom.Equiv

  λ⇒/ : ∀ {X Y} (J : Slice⇒₁ X Y) → Slice⇒₂ (id/ ⊚₀/ J) J
  λ⇒/ {X}{Y} J = slicearr₂ $ begin
    J.Δ                                   ≈⟨ introˡ id₂◁ ⟩
    (id₂ ◁ J.h) ∘ᵥ J.Δ                    ≈˘⟨ (unitʳ.iso.isoʳ (Y.arr , _) ⟩⊚⟨refl ⟩∘⟨refl) ⟩
    ((ρ⇒ ∘ᵥ ρ⇐) ◁ J.h) ∘ᵥ J.Δ             ≈˘⟨ (∘ᵥ-distr-◁ ⟩∘⟨refl) ⟩
    (ρ⇒ ◁ J.h ∘ᵥ ρ⇐ ◁ J.h) ∘ᵥ J.Δ         ≈⟨ pushˡ (sym triangle ⟩∘⟨ refl) ⟩
    (Y.arr ▷ λ⇒ ∘ᵥ α⇒) ∘ᵥ ρ⇐ ◁ J.h ∘ᵥ J.Δ ≈⟨ pullʳ (sym assoc) ⟩
    Y.arr ▷ λ⇒ ∘ᵥ (α⇒ ∘ᵥ ρ⇐ ◁ J.h) ∘ᵥ J.Δ ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module J = Slice⇒₁ J
          open 1Category (hom X.Y A)
          open HomReasoning
          open MR (hom X.Y A)
          open hom.Equiv

  ρ⇒/ : ∀{X}{Y} (J : Slice⇒₁ X Y) → Slice⇒₂ (J ⊚₀/ id/) J
  ρ⇒/ {X}{Y} J = slicearr₂ $ begin
    J.Δ                                     ≈⟨ introʳ (unitʳ.iso.isoʳ _) ⟩
    J.Δ ∘ᵥ ρ⇒ ∘ᵥ ρ⇐                         ≈⟨ pullˡ (sym ρ⇒-∘ᵥ-◁) ⟩
    (ρ⇒ ∘ᵥ J.Δ ◁ id₁) ∘ᵥ ρ⇐                 ≈⟨ unitorʳ-coherence  ⟩∘⟨refl ⟩∘⟨refl ⟩
    ((Y.arr ▷ ρ⇒ ∘ᵥ α⇒) ∘ᵥ J.Δ ◁ id₁) ∘ᵥ ρ⇐ ≈⟨ pushˡ assoc ⟩
    Y.arr ▷ ρ⇒ ∘ᵥ (α⇒ ∘ᵥ J.Δ ◁ id₁) ∘ᵥ ρ⇐   ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module J = Slice⇒₁ J
          open 1Category (hom X.Y A)
          open HomReasoning
          open MR (hom X.Y A)
          open hom.Equiv

  slice-inv : ∀ {X}{Y}{J : Slice⇒₁ X Y}{K} (α : Slice⇒₂ J K) → (f : Slice⇒₁.h K ⇒₂ Slice⇒₁.h J) → (f ∘ᵥ (Slice⇒₂.ϕ α) ≈ id₂) → Slice⇒₂ K J
  slice-inv {X}{Y}{J}{K} α f p = slicearr₂ $ begin
    J.Δ                               ≈⟨ introˡ ▷id₂ ⟩
    (Y.arr ▷ id₂) ∘ᵥ J.Δ              ≈˘⟨ (refl⟩⊚⟨ p ⟩∘⟨refl) ⟩
    (Y.arr ▷ (f ∘ᵥ α.ϕ)) ∘ᵥ J.Δ       ≈˘⟨ (∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
    (Y.arr ▷ f ∘ᵥ Y.arr ▷ α.ϕ) ∘ᵥ J.Δ ≈⟨ pullʳ (sym α.E) ⟩
    Y.arr ▷ f ∘ᵥ K.Δ                  ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module J = Slice⇒₁ J
          module K = Slice⇒₁ K
          module α = Slice⇒₂ α
          open 1Category (hom X.Y A)
          open HomReasoning
          open MR (hom X.Y A)
          open hom.Equiv

LaxSlice : Obj → Bicategory (o ⊔ ℓ) (ℓ ⊔ e) e (o ⊔ t)
LaxSlice A   = record
  { enriched = record
    { Obj = SliceObj A
    ; hom = SliceHomCat
    ; id = const id/
    ; ⊚ = _⊚/_
    ; ⊚-assoc = niHelper (record
      { η       = λ ((J , K) , L) → α⇒/ J K L
      ; η⁻¹     = λ ((J , K) , L) → slice-inv (α⇒/ J K L) α⇐ (⊚-assoc.iso.isoˡ _)
      ; commute = λ f → ⊚-assoc.⇒.commute _
      ; iso = λ _ → record { isoˡ = ⊚-assoc.iso.isoˡ _ ; isoʳ = ⊚-assoc.iso.isoʳ _ }
      })
    ; unitˡ = niHelper (record
      { η       = λ (_ , J) → λ⇒/ J
      ; η⁻¹     = λ (_ , J) → slice-inv (λ⇒/ J) λ⇐ (unitˡ.iso.isoˡ _)
      ; commute = λ _ → λ⇒-∘ᵥ-▷
      ; iso     = λ _ → record { isoˡ = unitˡ.iso.isoˡ _ ; isoʳ = unitˡ.iso.isoʳ _ }
      })
    ; unitʳ = niHelper (record
         { η       = λ (J , _) → ρ⇒/ J
         ; η⁻¹     = λ (J , _) → slice-inv (ρ⇒/ J) ρ⇐ (unitʳ.iso.isoˡ _)
         ; commute = λ _ → ρ⇒-∘ᵥ-◁
         ; iso     = λ _ → record { isoˡ = unitʳ.iso.isoˡ _ ; isoʳ = unitʳ.iso.isoʳ _ } })
    }
  ; triangle = triangle
  ; pentagon = pentagon
  }
  where open SliceHom A
