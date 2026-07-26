{-# OPTIONS --without-K --safe #-}

open import Categories.Category
import Categories.Diagram.Pullback as PB
open import Categories.Fibration.Base
open import Categories.Functor
open import Categories.Morphism.Cartesian using (Cartesian)
open import Data.Product using (_,_; proj₂)

module Categories.Fibration.CodomainFibration {o ℓ e}
  (C : Category o ℓ e)
  (pullbacks : ∀ {A B X} → (f : C [ A , X ]) → (g : C [ B , X ])
             → PB.Pullback C f g)
  where

open import Categories.Category.Construction.Arrow C
open import Categories.Diagram.Pullback C using (Pullback)
open import Categories.Morphism C using (module ≅)

private
  module C = Category C

open C.HomReasoning

Codomain : Functor Arrow C
Codomain = record
  { F₀ = Morphism.cod
  ; F₁ = Morphism⇒.cod⇒
  ; identity = C.Equiv.refl
  ; homomorphism = C.Equiv.refl
  ; F-resp-≈ = proj₂
  }

CodFibration : Fibration Codomain
CodFibration = record
  { X = X
  ; f = f
  ; φ = λ _ → ≅.refl
  ; u∘φ⁻≈pf = λ _ → C.identityʳ
  ; cartesian = cartesian
  }
  where

  pb : ∀ {I} {Y : Morphism} (u : C [ I , Morphism.cod Y ]) → Pullback u (Morphism.arr Y)
  pb {Y = Y} u = pullbacks u (Morphism.arr Y)

  X : ∀ {I} {Y : Morphism} (u : C [ I , Morphism.cod Y ]) → Morphism
  X {I} {Y} u = record
    { dom = Pullback.P (pb {Y = Y} u)
    ; cod = I
    ; arr = Pullback.p₁ (pb {Y = Y} u)
    }

  f : ∀ {I} {Y : Morphism} (u : C [ I , Morphism.cod Y ]) → Arrow [ X u , Y ]
  f {Y = Y} u = record
    { dom⇒ = Pullback.p₂ (pb {Y = Y} u)
    ; cod⇒ = u
    ; square = Pullback.commute (pb {Y = Y} u)
    }

  cartesian : ∀ {I} {Y : Morphism} (u : C [ I , Morphism.cod Y ]) → Cartesian Codomain (f {Y = Y} u)
  cartesian {Y = Y} u = record
    { universal = λ {A} {v} h eq → record
      { dom⇒ = Pullback.universal (pb {Y = Y} u) (universal-square h eq)
      ; cod⇒ = v
      ; square = C.Equiv.sym
          (Pullback.p₁∘universal≈h₁ (pb {Y = Y} u)
            {h₁ = v C.∘ Morphism.arr A}
            {h₂ = Morphism⇒.dom⇒ h}
            {eq = universal-square h eq})
      }
    ; commute = λ {A} {v} {h} eq →
      ( Pullback.p₂∘universal≈h₂ (pb {Y = Y} u) {eq = universal-square h eq}
      , eq
      )
    ; compat = λ _ → C.Equiv.refl
    }
    where
    universal-square : ∀ {A} {v : C [ Morphism.cod A , Morphism.cod (X {Y = Y} u) ]}
      (h : Arrow [ A , Y ])
      (eq : C [ C [ Morphism⇒.cod⇒ (f {Y = Y} u) ∘ v ] ≈ Morphism⇒.cod⇒ h ])
      → C [ C [ u ∘ C [ v ∘ Morphism.arr A ] ] ≈ C [ Morphism.arr Y ∘ Morphism⇒.dom⇒ h ] ]
    universal-square {A} {v} h eq =
      C.Equiv.trans C.sym-assoc
        (C.Equiv.trans (C.∘-resp-≈ˡ eq) (Morphism⇒.square h))
