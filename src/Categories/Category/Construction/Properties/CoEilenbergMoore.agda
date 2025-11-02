{-# OPTIONS --cubical-compatible --without-K --safe #-}
-- verbatim dual of Categories.Category.Construction.Properties.EilenbergMoore
module Categories.Category.Construction.Properties.CoEilenbergMoore where

open import Level
import Relation.Binary.PropositionalEquality.Core as ≡

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Equivalence
open import Categories.Comonad

open import Categories.NaturalTransformation.Core renaming (id to idN)
open import Categories.Morphism.HeterogeneousIdentity
open import Categories.Morphism.Reasoning

open import Categories.Adjoint.Construction.CoEilenbergMoore
open import Categories.Category.Construction.CoEilenbergMoore

private
  variable
    o ℓ e : Level
    𝒞 𝒟 : Category o ℓ e

module _ {F : Functor 𝒟 𝒞} {G : Functor 𝒞 𝒟} (F⊣G : Adjoint F G) where
  private
    T : Comonad 𝒞
    T = adjoint⇒comonad F⊣G

    coEM𝒞 : Category _ _ _
    coEM𝒞 = CoEilenbergMoore T

    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module coEM𝒞 = Category coEM𝒞

    open 𝒞.HomReasoning

    module T = Comonad T
    module F = Functor F
    module G = Functor G
    module FG = Functor (F ∘F G)

    open Adjoint F⊣G
    open NaturalTransformation
    open Category.Equiv

  -- Maclane's Comparison Functor
  ComparisonF : Functor 𝒟 coEM𝒞
  ComparisonF = record
   { F₀ = λ X → record
    { A = F.F₀ X
    ; coaction = F.F₁ (unit.η X)
    ; commute = commute-obj
    ; identity = zig
    }
   ; F₁ = λ {A} {B} f → record
    { arr = F.F₁ f
    ; commute = commute-mor
    }
   ; identity = F.identity
   ; homomorphism = F.homomorphism
   ; F-resp-≈ = F.F-resp-≈
   }
   where
    commute-obj : {X : Category.Obj 𝒟} → T.F.F₁ (F.F₁ (unit.η X)) 𝒞.∘ F.F₁ (unit.η X) 𝒞.≈ T.δ.η (F.F₀ X) 𝒞.∘ F.F₁ (unit.η X)
    commute-obj {X} = begin
      F.F₁ (G.F₁ (F.F₁ (unit.η X))) 𝒞.∘ F.F₁ (unit.η X) ≈⟨ sym 𝒞 (F.homomorphism) ⟩
      F.F₁ (G.F₁ (F.F₁ (unit.η X)) 𝒟.∘ unit.η X)        ≈⟨ Functor.F-resp-≈ F (unit.sym-commute (unit.η X)) ⟩
      F.F₁ (unit.η (G.F₀ (F.F₀ X)) 𝒟.∘ unit.η X)        ≈⟨ F.homomorphism ⟩
      T.δ.η (F.F₀ X) 𝒞.∘ F.F₁ (unit.η X)                ∎
    commute-mor : {A B : Category.Obj 𝒟} {f : 𝒟 [ A , B ]} → F.F₁ (unit.η B) 𝒞.∘ F.F₁ f 𝒞.≈ T.F.F₁ (F.F₁ f) 𝒞.∘ F.F₁ (unit.η A)
    commute-mor {A} {B} {f} = begin
     F.F₁ (unit.η B) 𝒞.∘ F.F₁ f          ≈⟨ sym 𝒞 (F.homomorphism) ⟩
     F.F₁ (unit.η B 𝒟.∘ f)               ≈⟨ Functor.F-resp-≈ F (unit.commute f) ⟩
     F.F₁ (G.F₁ (F.F₁ f) 𝒟.∘ unit.η A)   ≈⟨ F.homomorphism ⟩
     T.F.F₁ (F.F₁ f) 𝒞.∘ F.F₁ (unit.η A) ∎

  Comparison∘F≡Free : (ComparisonF ∘F G) ≡F Cofree T
  Comparison∘F≡Free = record
   { eq₀ = λ X → ≡.refl
   ; eq₁ = λ f → id-comm-sym 𝒞
   }

  Forgetful∘ComparisonF≡G : (Forgetful T ∘F ComparisonF) ≡F F
  Forgetful∘ComparisonF≡G = record
   { eq₀ = λ X → ≡.refl
   ; eq₁ = λ f → id-comm-sym 𝒞
   }
