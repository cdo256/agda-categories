{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor
open import Categories.Fibration.Base
open import Categories.Morphism.Cartesian using (Cartesian)
open import Data.Product using (Σ; _,_; proj₁)
open import Level

module Categories.Fibration.CodomainFibration where

open import Categories.Category.Instance.Sets
open import Categories.Category.Construction.Arrow
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

Sets⃗ : ∀ ℓ → Category (suc ℓ) ℓ ℓ
Sets⃗ ℓ = Arrow (Sets ℓ)

cod₀ : ∀ {ℓ} → Morphism (Sets ℓ) → Set ℓ
cod₀ = Morphism.cod
cod₁ : ∀ {ℓ} {A B} → Sets⃗ ℓ [ A , B ] → Sets ℓ [ cod₀ A , cod₀ B ]
cod₁ f = Morphism⇒.cod⇒ f

cod : ∀ ℓ → Functor (Sets⃗ ℓ) (Sets ℓ)
cod ℓ = record
  { F₀ = cod₀
  ; F₁ = cod₁
  ; identity = λ _ → ≡.refl
  ; homomorphism = λ _ → ≡.refl
  ; F-resp-≈ = λ (_ , r) → r
  }

CodFibration : ∀ ℓ → Fibration (cod ℓ)
CodFibration ℓ = record
  { X = X
  ; f = f
  ; φ = λ _ → ≅.refl
  ; u∘φ⁻≈pf = λ _ _ → ≡.refl
  ; cartesian = cartesian
  }
  where

  open import Categories.Morphism (Sets ℓ) using (module ≅)

  PullbackDom : ∀ {I : Set ℓ} (Y : Morphism (Sets ℓ)) (u : I → cod₀ Y) → Set ℓ
  PullbackDom {I} Y u = Σ I λ i → Σ (Morphism.dom Y) λ y → u i ≡ Morphism.arr Y y

  X : ∀ {I : Set ℓ} {Y : Morphism (Sets ℓ)} (u : I → cod₀ Y)
    → Morphism (Sets ℓ)
  X {I} {Y} u = record
    { dom = PullbackDom Y u
    ; cod = I
    ; arr = proj₁
    }

  f : ∀ {I : Set ℓ} {Y : Morphism (Sets ℓ)} (u : I → cod₀ Y) → Sets⃗ ℓ [ X u , Y ]
  f {Y = Y} u = record
    { dom⇒ = λ where (_ , (y , _)) → y
    ; cod⇒ = u
    ; square = λ where (_ , (_ , eq)) → eq
    }

  cartesian : ∀ {I : Set ℓ} {Y : Morphism (Sets ℓ)} (u : I → cod₀ Y)
    → Cartesian (cod ℓ) (f {Y = Y} u)
  cartesian {Y = Y} u = record
    { universal = λ {A} {v} h eq → record
      { dom⇒ = λ a →
          ( v (Morphism.arr A a)
          , ( Morphism⇒.dom⇒ h a
            , ≡.trans (eq (Morphism.arr A a)) (Morphism⇒.square h a)
            )
          )
      ; cod⇒ = v
      ; square = λ _ → ≡.refl
      }
    ; commute = λ {A} {v} {h} eq →
        ( (λ _ → ≡.refl)
        , eq
        )
    ; compat = λ _ _ → ≡.refl
    }
