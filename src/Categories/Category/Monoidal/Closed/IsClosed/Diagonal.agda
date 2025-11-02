{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Closed

module Categories.Category.Monoidal.Closed.IsClosed.Diagonal
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Product using (Σ; _,_)
open import Function using (_$_) renaming (_∘_ to _∙_)

open import Categories.Category.Product
open import Categories.Category.Monoidal.Properties M
open import Categories.Morphism C
open import Categories.Morphism.Properties C
open import Categories.Morphism.Reasoning C
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Bifunctor.Properties
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Dinatural hiding (_∘ʳ_)
open import Categories.NaturalTransformation.NaturalIsomorphism as NI hiding (refl)
import Categories.Category.Closed as Cls

open Closed Cl

private
  open Category C
  module ℱ = Functor
  α⇒ = associator.from
  α⇐ = associator.to
  λ⇒ = unitorˡ.from
  λ⇐ = unitorˡ.to
  ρ⇒ = unitorʳ.from
  ρ⇐ = unitorʳ.to

open HomReasoning
open Equiv
open adjoint renaming (unit to η; counit to ε; Ladjunct to 𝕃; Ladjunct-comm′ to 𝕃-comm′;
 Ladjunct-resp-≈ to 𝕃-resp-≈)

open import Categories.Category.Monoidal.Closed.IsClosed.Identity Cl  -- defines diagonal
open import Categories.Category.Monoidal.Closed.IsClosed.L Cl

Lj≈j : ∀ {X Y} → L X Y Y ∘ diagonal.α Y ≈ diagonal.α [ X , Y ]₀
Lj≈j {X} {Y} = begin
  L X Y Y ∘ 𝕃 λ⇒                                          ≈˘⟨ 𝕃-comm′ ⟩
  𝕃 (𝕃 (ε.η Y ∘ id ⊗₁ ε.η Y ∘ α⇒) ∘ 𝕃 λ⇒ ⊗₁ id)           ≈˘⟨ 𝕃-resp-≈ 𝕃-comm′ ⟩
  𝕃 (𝕃 $ (ε.η Y ∘ id ⊗₁ ε.η Y ∘ α⇒) ∘ (𝕃 λ⇒ ⊗₁ id) ⊗₁ id) ≈⟨ 𝕃-resp-≈ $ 𝕃-resp-≈ $ absorb-λ⇒ ⟩
  𝕃 (𝕃 (Radjunct λ⇒))                                     ≈⟨ 𝕃-resp-≈ LRadjunct≈id ⟩
  diagonal.α [ X , Y ]₀                                   ∎
  where
  absorb-λ⇒ : (ε.η Y ∘ id ⊗₁ ε.η {X} Y ∘ α⇒) ∘ (𝕃 λ⇒ ⊗₁ id) ⊗₁ id ≈ Radjunct λ⇒
  absorb-λ⇒ = begin
    (ε.η Y ∘ id ⊗₁ ε.η Y ∘ α⇒) ∘ (𝕃 λ⇒ ⊗₁ id) ⊗₁ id ≈⟨ pull-last assoc-commute-from ⟩
    ε.η Y ∘ id ⊗₁ ε.η Y ∘ 𝕃 λ⇒ ⊗₁ id ⊗₁ id ∘ α⇒     ≈⟨ sym-assoc ⟩
    (ε.η Y ∘ id ⊗₁ ε.η Y) ∘ 𝕃 λ⇒ ⊗₁ id ⊗₁ id ∘ α⇒   ≈⟨ refl⟩∘⟨ ⊗.F-resp-≈ (refl , ⊗.identity) ⟩∘⟨refl ⟩
    (ε.η Y ∘ id ⊗₁ ε.η Y) ∘ 𝕃 λ⇒ ⊗₁ id ∘ α⇒         ≈⟨ center [ ⊗ ]-commute ⟩
    ε.η Y ∘ (𝕃 λ⇒ ⊗₁ id ∘ id ⊗₁ ε.η Y) ∘ α⇒         ≈⟨ pull-first RLadjunct≈id ⟩
    λ⇒ ∘ id ⊗₁ ε.η Y ∘ α⇒                           ≈⟨ pullˡ unitorˡ-commute-from ⟩
    (ε.η Y ∘ λ⇒) ∘ α⇒                               ≈⟨ pullʳ coherence₁ ⟩
    Radjunct λ⇒                                     ∎

jL≈i : {X Y : Obj} → [ diagonal.α X , id ]₁ ∘ L X X Y ≈ identity.⇒.η [ X , Y ]₀
jL≈i {X} {Y} = begin
  [ Δ X , id ]₁ ∘ L X X Y                          ≈˘⟨ pushˡ [ [-,-] ]-commute ⟩
  ([ id , 𝕃 inner ]₁ ∘ [ Δ X , id ]₁) ∘ η.η XY     ≈˘⟨ pushʳ (mate.commute₁ (diagonal.α X)) ⟩
  [ id , 𝕃 inner ]₁ ∘ [ id , id ⊗₁ Δ X ]₁ ∘ η.η XY ≈˘⟨ pushˡ (ℱ.homomorphism [ unit ,-]) ⟩
  𝕃 (𝕃 inner ∘ id ⊗₁ Δ X)                          ≈˘⟨ 𝕃-resp-≈ $ 𝕃-comm′ ⟩
  𝕃 (𝕃 $ inner ∘ (id ⊗₁ Δ X) ⊗₁ id)                ≈⟨ 𝕃-resp-≈ $ 𝕃-resp-≈ inner∘diag⇒ℝρ ⟩
  𝕃 (𝕃 $ Radjunct ρ⇒)                              ≈⟨ 𝕃-resp-≈ $ LRadjunct≈id ⟩
  𝕃 ρ⇒                                             ≈˘⟨ identityˡ ⟩
  id ∘ 𝕃 ρ⇒                                        ∎
  where
  XY    = [ X , Y ]₀
  inner = ε.η Y ∘ id ⊗₁ ε.η X ∘ α⇒
  Δ     = diagonal.α
  inner∘diag⇒ℝρ : inner ∘ (id ⊗₁ Δ X) ⊗₁ id ≈ Radjunct ρ⇒
  inner∘diag⇒ℝρ = begin
    inner ∘ (id ⊗₁ Δ X) ⊗₁ id                    ≈⟨ pull-last assoc-commute-from ○ sym-assoc ⟩
    (ε.η Y ∘ id ⊗₁ ε.η X) ∘ id ⊗₁ Δ X ⊗₁ id ∘ α⇒ ≈⟨ center (⟺ (ℱ.homomorphism (XY ⊗-))) ⟩
    ε.η Y ∘ id ⊗₁ (ε.η X ∘ 𝕃 λ⇒ ⊗₁ id) ∘ α⇒      ≈⟨ refl⟩∘⟨ ℱ.F-resp-≈ (XY ⊗-) RLadjunct≈id ⟩∘⟨refl ⟩
    ε.η Y ∘ id ⊗₁ λ⇒ ∘ α⇒                        ≈⟨ refl⟩∘⟨ triangle ⟩
    Radjunct ρ⇒                                  ∎

private
  i-η = identity.⇒.η

-- Not about diagonal, but it feels like a waste to start another file just for this
iL≈i : {Y Z : Obj} → [ i-η Y , id ]₁ ∘ L unit Y Z ≈ [ id , i-η Z ]₁
iL≈i {Y} {Z} = begin
  [ i-η Y , id ]₁ ∘ L unit Y Z                      ≈˘⟨ pushˡ [ [-,-] ]-commute ⟩
  ([ id , 𝕃 inner ]₁ ∘ [ i-η Y , id ]₁) ∘ η.η YZ    ≈⟨ ( refl⟩∘⟨ (ℱ.F-resp-≈ [-, YZ ⊗₀ [ unit , Y ]₀ ] identityˡ)) ⟩∘⟨refl ⟩
  ([ id , 𝕃 inner ]₁ ∘ [ 𝕃 ρ⇒ , id ]₁) ∘ η.η YZ     ≈˘⟨ pushʳ (mate.commute₁ (𝕃 ρ⇒)) ⟩
  [ id , 𝕃 inner ]₁ ∘ [ id , id ⊗₁ 𝕃 ρ⇒ ]₁ ∘ η.η YZ ≈˘⟨ pushˡ (ℱ.homomorphism [ Y ,-]) ⟩
  𝕃 (𝕃 inner ∘ id ⊗₁ 𝕃 ρ⇒)                          ≈˘⟨ 𝕃-resp-≈ 𝕃-comm′ ⟩
  𝕃 (𝕃 $ inner ∘ (id ⊗₁ 𝕃 ρ⇒) ⊗₁ id)                ≈⟨ 𝕃-resp-≈ $ 𝕃-resp-≈ absorb ⟩
  𝕃 (𝕃 $ ε.η Z ∘ ρ⇒)                                ≈⟨ 𝕃-resp-≈ $ ∘-resp-≈ˡ (ℱ.homomorphism [ unit ,-])
                                                                  ○ (assoc ○ ∘-resp-≈ʳ (⟺ identityˡ)) ⟩
  𝕃 ([ id , ε.η Z ]₁ ∘ i-η (YZ ⊗₀ Y))               ≈˘⟨ 𝕃-resp-≈ $ identity.⇒.commute (ε.η Z) ⟩
  𝕃 (i-η Z ∘ ε.η Z)                                 ≈˘⟨ 𝕃-resp-≈ $ ε.commute (i-η Z) ⟩
  𝕃 (Radjunct [ id , i-η Z ]₁)                      ≈⟨ LRadjunct≈id ⟩
  [ id , i-η Z ]₁                                   ∎
  where
  YZ    = [ Y , Z ]₀
  inner = ε.η Z ∘ id ⊗₁ ε.η Y ∘ α⇒
  absorb : inner ∘ (id ⊗₁ 𝕃 ρ⇒) ⊗₁ id ≈ ε.η Z ∘ ρ⇒
  absorb = begin
    inner ∘ (id ⊗₁ 𝕃 ρ⇒) ⊗₁ id                    ≈⟨ pull-last assoc-commute-from ○ sym-assoc ⟩
    (ε.η Z ∘ id ⊗₁ ε.η Y) ∘ id ⊗₁ 𝕃 ρ⇒ ⊗₁ id ∘ α⇒ ≈⟨ center (⟺ (ℱ.homomorphism (YZ ⊗-))) ⟩
    ε.η Z ∘ id ⊗₁ (ε.η Y ∘ 𝕃 ρ⇒ ⊗₁ id) ∘ α⇒       ≈⟨ refl⟩∘⟨ ℱ.F-resp-≈ (YZ ⊗-) RLadjunct≈id ⟩∘⟨refl ⟩
    ε.η Z ∘ id ⊗₁ ρ⇒ ∘ α⇒                         ≈⟨ refl⟩∘⟨ coherence₂ ⟩
    ε.η Z ∘ ρ⇒                                    ∎
