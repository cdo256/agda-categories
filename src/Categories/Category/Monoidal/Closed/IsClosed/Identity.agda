{-# OPTIONS --cubical-compatible --without-K --safe #-}

-- There are really all 'private' sub-pieces of
-- Categories.Category.Monoidal.Closed.IsClosed, but that is taking
-- forever to typecheck, so the idea is to split things into pieces and
-- hope that that will help.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Category.Monoidal.Closed.IsClosed.Identity
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Function using (_$_) renaming (_∘_ to _∙_)

open import Categories.Category.Monoidal.Utilities M
open import Categories.Morphism C using (Iso)
open import Categories.Morphism.Properties C using (Iso-resp-≈)
open import Categories.Morphism.Reasoning C using (pullʳ; pullˡ; pushˡ; cancelʳ)
open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Bifunctor.Properties
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Dinatural
  using (Extranaturalʳ; extranaturalʳ; DinaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism)
import Categories.Category.Closed as Cls

open Closed Cl
open Category C       -- most of it is used

open HomReasoning
open adjoint renaming (unit to η; counit to ε; Ladjunct to 𝕃)

private
  λ⇒ = unitorˡ.from
  λ⇐ = unitorˡ.to
  ρ⇒ = unitorʳ.from
  ρ⇐ = unitorʳ.to

identity : NaturalIsomorphism idF [ unit ,-]
identity = record
  { F⇒G = F∘id⇒F ∘ᵥ ([ unit ,-] ∘ˡ (unitorʳ-natural.F⇒G)) ∘ᵥ η
  ; F⇐G = ε ∘ᵥ (unitorʳ-natural.F⇐G ∘ʳ [ unit ,-]) ∘ᵥ F⇒id∘F
  ; iso = λ X → Iso-resp-≈ (iso X) (⟺ identityˡ) (⟺ (∘-resp-≈ʳ identityʳ))
  }
  where
  open Functor
  iso : ∀ X → Iso (𝕃 unitorʳ.from) (ε.η X ∘ unitorʳ.to)
  iso X = record
    { isoˡ = begin
      (ε.η X ∘ ρ⇐) ∘ 𝕃 ρ⇒      ≈⟨ pullʳ unitorʳ-commute-to ⟩
      ε.η X ∘ 𝕃 ρ⇒ ⊗₁ id ∘ ρ⇐  ≈⟨ sym-assoc ⟩
      Radjunct (𝕃 ρ⇒) ∘ ρ⇐     ≈⟨ RLadjunct≈id ⟩∘⟨refl ⟩
      ρ⇒ ∘ ρ⇐                  ≈⟨ unitorʳ.isoʳ ⟩
      id                       ∎
    ; isoʳ = begin
      𝕃 ρ⇒ ∘ ε.η X ∘ ρ⇐                      ≈⟨ pullʳ (η.commute _) ⟩
      [ id , ρ⇒ ]₁ ∘ 𝕃 ((ε.η X ∘ ρ⇐) ⊗₁ id) ≈˘⟨ pushˡ (homomorphism [ unit ,-]) ⟩
      𝕃 (ρ⇒ ∘ (ε.η X ∘ ρ⇐) ⊗₁ id)           ≈⟨ F-resp-≈ [ unit ,-] unitorʳ-commute-from ⟩∘⟨refl ⟩
      𝕃 ((ε.η X ∘ ρ⇐) ∘ ρ⇒)                 ≈⟨ F-resp-≈ [ unit ,-] (cancelʳ unitorʳ.isoˡ) ⟩∘⟨refl ⟩
      𝕃 (ε.η X)                              ≈⟨ zag ⟩
      id                                     ∎
    }

module identity = NaturalIsomorphism identity

diagonal : Extranaturalʳ unit [-,-]
diagonal = extranaturalʳ (λ X → 𝕃 λ⇒)
  $ λ {X Y f} → begin
    [ id , f ]₁ ∘ 𝕃 λ⇒                             ≈˘⟨ pushˡ (homomorphism [ X ,-]) ⟩
    [ id , f ∘ λ⇒ ]₁ ∘ η.η unit                    ≈˘⟨ F-resp-≈ [ X ,-] unitorˡ-commute-from ⟩∘⟨refl ⟩
    [ id , λ⇒ ∘ id ⊗₁ f ]₁ ∘ η.η unit              ≈⟨ homomorphism [ X ,-] ⟩∘⟨refl ⟩
    ([ id , λ⇒ ]₁ ∘ [ id , id ⊗₁ f ]₁) ∘ η.η unit  ≈⟨ pullʳ (mate.commute₁ f) ⟩
    [ id , λ⇒ ]₁ ∘ [ f , id ]₁ ∘ η.η unit          ≈⟨ pullˡ [ [-,-] ]-commute ⟩
    ([ f , id ]₁ ∘ [ id , λ⇒ ]₁) ∘ η.η unit        ≈⟨ assoc ⟩
    [ f , id ]₁ ∘ 𝕃 λ⇒                             ∎
  where open Functor

module diagonal = DinaturalTransformation diagonal
