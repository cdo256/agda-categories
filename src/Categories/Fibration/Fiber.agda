{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Fibration.Base
open import Categories.Functor hiding (id)
open import Categories.Morphism.Cartesian using (Cartesian)
open import Data.Product
open import Function.Structures using (IsBijection)
open import Level

module Categories.Fibration.Fiber {o ℓ e o′ ℓ′ e′} {𝐄 : Category o ℓ e} {𝐁 : Category o′ ℓ′ e′} (p : Functor 𝐄 𝐁) where

open import Categories.Morphism 𝐁 using (_≅_; module ≅)

private
  module 𝐄 = Category 𝐄
  module 𝐁 = Category 𝐁
  open Functor p renaming (F₀ to p₀; F₁ to p₁; homomorphism to p-hom)

record FiberObj (I : 𝐁.Obj) : Set (o ⊔ ℓ′ ⊔ e′) where
  field
    ob : 𝐄.Obj
    θ : p₀ ob ≅ I
  module θ = _≅_ θ

fiberObj₀ : (X : 𝐄.Obj) → FiberObj (p₀ X)
fiberObj₀ X = record
  { ob = X
  ; θ = ≅.refl
  }

record FiberHom {I} (X Y : FiberObj I) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
  private
    module X = FiberObj X
    module Y = FiberObj Y

  field
    hom : X.ob 𝐄.⇒ Y.ob
    iso : Y.θ.from 𝐁.∘ p₁ hom 𝐁.≈ X.θ.from

_≈_ : ∀ {I} → {X Y : FiberObj I} (f g : FiberHom X Y) → Set e
f ≈ g = FiberHom.hom f 𝐄.≈ FiberHom.hom g

Fiber : 𝐁.Obj → Category (o ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) e
Fiber I = record
  { Obj = FiberObj I
  ; _⇒_ = FiberHom
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = 𝐄.assoc
  ; sym-assoc = 𝐄.sym-assoc
  ; identityˡ = 𝐄.identityˡ
  ; identityʳ = 𝐄.identityʳ
  ; identity² = 𝐄.identity²
  ; equiv = record
    { refl = 𝐄.Equiv.refl
    ; sym = 𝐄.Equiv.sym
    ; trans = 𝐄.Equiv.trans
    }
  ; ∘-resp-≈ = 𝐄.∘-resp-≈
  }
  where

  id : ∀ {X} → FiberHom X X
  id = record
    { hom = 𝐄.id
    ; iso = 𝐁.∘-resp-≈ʳ identity .𝐁.Equiv.trans 𝐁.identityʳ
    }

  _∘_ : ∀ {X Y Z} → FiberHom Y Z → FiberHom X Y → FiberHom X Z
  _∘_ {X} {Y} {Z} g f = record
    { hom = g.hom 𝐄.∘ f.hom
    ; iso = iso
    }
    where
    module X = FiberObj X
    module Y = FiberObj Y
    module Z = FiberObj Z
    module f = FiberHom f
    module g = FiberHom g
    open 𝐁.HomReasoning
    iso : Z.θ.from 𝐁.∘ p₁ (g.hom 𝐄.∘ f.hom) 𝐁.≈ X.θ.from
    iso = begin
      Z.θ.from 𝐁.∘ p₁ (g.hom 𝐄.∘ f.hom)
        ≈⟨ 𝐁.∘-resp-≈ʳ p-hom ⟩
      Z.θ.from 𝐁.∘ (p₁ g.hom 𝐁.∘ p₁ f.hom)
        ≈⟨ 𝐁.sym-assoc ⟩
      (Z.θ.from 𝐁.∘ p₁ g.hom) 𝐁.∘ p₁ f.hom
        ≈⟨ 𝐁.∘-resp-≈ˡ g.iso ⟩
      Y.θ.from 𝐁.∘ p₁ f.hom
        ≈⟨ f.iso ⟩
      X.θ.from ∎
