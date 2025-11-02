{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Closed

module Categories.Category.Monoidal.Closed.IsClosed.Dinatural
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
  α⇒ = associator.from
  α⇐ = associator.to
  module ℱ = Functor

open HomReasoning
open Equiv
open adjoint renaming (unit to η; counit to ε; Ladjunct to 𝕃; Ladjunct-comm′ to 𝕃-comm′;
 Ladjunct-resp-≈ to 𝕃-resp-≈)

open import Categories.Category.Monoidal.Closed.IsClosed.Identity Cl
open import Categories.Category.Monoidal.Closed.IsClosed.L Cl

private
  id² : {S T : Obj} → [ S , T ]₀ ⇒ [ S , T ]₀
  id² = [ id , id ]₁

L-dinatural-comm :  ∀ {X′ Y Z X f} → [ [ f , id ]₁ , id² ]₁ ∘ L X′ Y Z ≈ [ id² , [ f , id ]₁ ]₁ ∘ L X Y Z
L-dinatural-comm {X′} {Y} {Z} {X} {f} = begin
  [ fˡ , id² ]₁ ∘ L X′ Y Z                              ≈⟨ [-,-].F-resp-≈ (refl , [-,-].identity) ⟩∘⟨refl ⟩
  [ fˡ , id ]₁ ∘ L X′ Y Z                               ≈˘⟨ pushˡ [ [-,-] ]-commute ⟩
  ([ id , 𝕃 L-inner ]₁ ∘ [ fˡ , id ]₁) ∘ η.η YZ         ≈˘⟨ pushʳ (mate.commute₁ [ f , id ]₁) ⟩
  [ id , 𝕃 L-inner ]₁ ∘ 𝕃 (id ⊗₁ fˡ)                    ≈˘⟨ pushˡ (ℱ.homomorphism [ XY ,-]) ⟩
  𝕃 (𝕃 L-inner ∘ id ⊗₁ fˡ)                              ≈˘⟨ 𝕃-resp-≈ 𝕃-comm′ ⟩
  𝕃 (𝕃 $ L-inner ∘ (id ⊗₁ fˡ) ⊗₁ id)                   ≈⟨ 𝕃-resp-≈ $ 𝕃-resp-≈ push-f-right ⟩
  𝕃 (𝕃 $ L-inner ∘ (id ⊗₁ id) ⊗₁ f)                    ≈⟨ 𝕃-resp-≈ $ pushˡ (ℱ.homomorphism [ X′ ,-]) ⟩
  𝕃 ([ id , L-inner {X} ]₁ ∘ 𝕃 ((id ⊗₁ id) ⊗₁ f))       ≈⟨ 𝕃-resp-≈ $ ∘-resp-≈ʳ (∘-resp-≈ˡ (X′-resp-≈ (⊗.F-resp-≈ (⊗.identity , refl))) ○ mate.commute₁ f) ⟩
  𝕃 ([ id , L-inner {X} ]₁ ∘ fˡ ∘ η.η (YZ ⊗₀ XY))        ≈⟨ 𝕃-resp-≈ $ pullˡ [ [-,-] ]-commute ○ assoc ⟩
  𝕃 (fˡ ∘ 𝕃 L-inner)                                     ≈⟨ ∘-resp-≈ˡ (ℱ.homomorphism [ XY ,-]) ○ assoc ⟩
  [ id , fˡ ]₁ ∘ L X Y Z                                 ≈˘⟨ [-,-].F-resp-≈ ([-,-].identity , refl) ⟩∘⟨refl ⟩
  [ id² , fˡ ]₁ ∘ L X Y Z                                ∎
  where
  fˡ        : ∀ {W} → [ X , W ]₀ ⇒ [ X′ , W ]₀
  fˡ        = [ f , id ]₁
  XY        = [ X , Y ]₀
  YZ        = [ Y , Z ]₀
  X′-resp-≈ = ℱ.F-resp-≈ [ X′ ,-]
  L-inner     : ∀ {W} → ([ Y , Z ]₀ ⊗₀ [ W , Y ]₀) ⊗₀ W ⇒ Z
  L-inner {W} = ε.η Z ∘ (id ⊗₁ ε.η {W} Y) ∘ α⇒
  push-f-right : (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ α⇒) ∘ (id ⊗₁ fˡ) ⊗₁ id ≈ (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ α⇒) ∘ (id ⊗₁ id) ⊗₁ f
  push-f-right = begin
    (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ α⇒) ∘ (id ⊗₁ fˡ) ⊗₁ id     ≈⟨ pull-last assoc-commute-from ⟩
    ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ id ⊗₁ fˡ ⊗₁ id ∘ α⇒         ≈˘⟨ refl⟩∘⟨ pushˡ (ℱ.homomorphism (YZ ⊗-)) ⟩
    ε.η Z ∘ id ⊗₁ (ε.η Y ∘ fˡ ⊗₁ id) ∘ α⇒               ≈⟨ refl⟩∘⟨ ℱ.F-resp-≈ (YZ ⊗-) (mate.commute₂ f) ⟩∘⟨refl ⟩
    ε.η Z ∘ id ⊗₁ (ε.η Y ∘ id ⊗₁ f) ∘ α⇒                ≈⟨ refl⟩∘⟨ ℱ.homomorphism (YZ ⊗-) ⟩∘⟨refl ⟩
    ε.η Z ∘ (id ⊗₁ ε.η Y ∘ id ⊗₁ id ⊗₁ f) ∘ α⇒          ≈⟨ center⁻¹ refl (⟺ assoc-commute-from) ○ pullˡ assoc ⟩
    (ε.η Z ∘ id ⊗₁ ε.η Y ∘ α⇒) ∘ (id ⊗₁ id) ⊗₁ f        ∎
