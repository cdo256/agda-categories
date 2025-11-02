{-# OPTIONS --cubical-compatible --without-K --safe #-}
-- verbatim dual of Categories.Category.Construction.Properties.Kleisli
module Categories.Category.Construction.Properties.CoKleisli where

open import Level
import Relation.Binary.PropositionalEquality as ≡

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Equivalence
open import Categories.Comonad
import Categories.Morphism.Reasoning as MR

open import Categories.Adjoint.Construction.CoKleisli
open import Categories.Category.Construction.CoKleisli

private
  variable
    o ℓ e : Level
    𝒞 𝒟 : Category o ℓ e

module _ {F : Functor 𝒞 𝒟} {G : Functor 𝒟 𝒞} (F⊣G : Adjoint F G) where
  private
    T : Comonad 𝒟
    T = adjoint⇒comonad F⊣G

    𝒟ₜ : Category _ _ _
    𝒟ₜ = CoKleisli T

    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module 𝒟ₜ = Category 𝒟ₜ


    module T = Comonad T
    module F = Functor F
    module G = Functor G

    open Adjoint F⊣G

  -- Maclane's Comparison Functor
  ComparisonF : Functor 𝒟ₜ 𝒞
  ComparisonF = record
   { F₀ = λ X → G.F₀ X
   ; F₁ = λ {A} {B} f → 𝒞 [ (G.F₁ f) ∘ unit.η (G.F₀ A) ]
   ; identity = λ {A} → zag
   ; homomorphism = λ {X} {Y} {Z} {f} {g} → begin
      G.F₁ (g 𝒟.∘ F.F₁ (G.F₁ f) 𝒟.∘ F.F₁ (unit.η (G.F₀ X))) 𝒞.∘ unit.η (G.F₀ X)             ≈⟨ pushˡ G.homomorphism ⟩
      G.F₁ g 𝒞.∘ G.F₁ ((F.F₁ (G.F₁ f)) 𝒟.∘ F.F₁ (unit.η (G.F₀ X))) 𝒞.∘ unit.η (G.F₀ X)      ≈⟨ (refl⟩∘⟨ pushˡ G.homomorphism) ⟩
      G.F₁ g 𝒞.∘ G.F₁ (F.F₁ (G.F₁ f)) 𝒞.∘ G.F₁ (F.F₁ (unit.η (G.F₀ X))) 𝒞.∘ unit.η (G.F₀ X) ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ sym (unit.commute (unit.η (G.F₀ X))))) ⟩
      G.F₁ g 𝒞.∘ G.F₁ (F.F₁ (G.F₁ f)) 𝒞.∘ unit.η (G.F₀ (F.F₀ (G.F₀ X))) 𝒞.∘ unit.η (G.F₀ X) ≈⟨ (refl⟩∘⟨ pullˡ (sym (unit.commute (G.F₁ f)))) ⟩
      G.F₁ g 𝒞.∘ (unit.η (G.F₀ Y) 𝒞.∘ G.F₁ f) 𝒞.∘ unit.η (G.F₀ X)                           ≈⟨ MR.assoc²δγ 𝒞 ⟩
      (G.F₁ g 𝒞.∘ unit.η (G.F₀ Y)) 𝒞.∘ G.F₁ f 𝒞.∘ unit.η (G.F₀ X)                           ∎
   ; F-resp-≈ = λ eq → 𝒞.∘-resp-≈ (G.F-resp-≈ eq) (Category.Equiv.refl 𝒞)
   }
   where
    open 𝒞.HomReasoning
    open 𝒞.Equiv
    open MR 𝒞

  private
    L = ComparisonF
    module L = Functor L
    module Gₜ = Functor (Forgetful T)
    module Fₜ = Functor (Cofree T)

  F∘L≡Forgetful : (F ∘F L) ≡F Forgetful T
  F∘L≡Forgetful = record
   { eq₀ = λ X → ≡.refl
   ; eq₁ = eq-1
   }
   where
   open 𝒟.HomReasoning
   open MR 𝒟
   eq-1 : {X Y : 𝒟.Obj} (f : F.F₀ (G.F₀ X) 𝒟.⇒ Y) → 𝒟.id 𝒟.∘ F.F₁ (G.F₁ f 𝒞.∘ unit.η (G.F₀ X)) 𝒟.≈ (F.F₁ (G.F₁ f) 𝒟.∘ F.F₁ (unit.η (G.F₀ X))) 𝒟.∘ 𝒟.id
   eq-1 {X} {Y} f = begin
    𝒟.id 𝒟.∘ F.F₁ (G.F₁ f 𝒞.∘ unit.η (G.F₀ X))          ≈⟨ id-comm-sym ⟩
    F.F₁ (G.F₁ f 𝒞.∘ unit.η (G.F₀ X)) 𝒟.∘ 𝒟.id          ≈⟨ (F.homomorphism ⟩∘⟨refl) ⟩
    (F.F₁ (G.F₁ f) 𝒟.∘ F.F₁ (unit.η (G.F₀ X))) 𝒟.∘ 𝒟.id ∎

  L∘Cofree≡G : (L ∘F Cofree T) ≡F G
  L∘Cofree≡G = record
   { eq₀ = λ X → ≡.refl
   ; eq₁ = eq-1
   }
   where
   open 𝒞.HomReasoning
   open MR 𝒞
   eq-1 : {X Y : 𝒟.Obj} (f : X 𝒟.⇒ Y) → 𝒞.id 𝒞.∘ G.F₁ (f 𝒟.∘ counit.η X) 𝒞.∘ unit.η (G.F₀ X) 𝒞.≈ G.F₁ f 𝒞.∘ 𝒞.id
   eq-1 {X} {Y} f = begin
    𝒞.id 𝒞.∘ G.F₁ (f 𝒟.∘ counit.η X) 𝒞.∘ unit.η (G.F₀ X)         ≈⟨ id-comm-sym ⟩
    (G.F₁ (f 𝒟.∘ counit.η X) 𝒞.∘ unit.η (G.F₀ X)) 𝒞.∘ 𝒞.id       ≈⟨ (pushˡ G.homomorphism ⟩∘⟨refl) ⟩
    (G.F₁ f 𝒞.∘ G.F₁ (counit.η X) 𝒞.∘ unit.η (G.F₀ X)) 𝒞.∘ 𝒞.id  ≈⟨ (elimʳ zag ⟩∘⟨refl) ⟩
    G.F₁ f 𝒞.∘ 𝒞.id                                              ∎
