{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Closed

module Categories.Category.Monoidal.Closed.IsClosed.Pentagon
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
  module C = Category C
  open Category C
  open Commutation C
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

open import Categories.Category.Monoidal.Closed.IsClosed.Identity Cl
open import Categories.Category.Monoidal.Closed.IsClosed.L Cl

-- some intermediate steps as lemmas

private
-- ⊗.F₀ (⊗.F₀ ([-,-].F₀ (u , v) , [-,-].F₀ (x , u)) , x) ⇒ v
  inner : {x : Obj} (v u : Obj) → ((Functor.F₀ [ u ,-] v) ⊗₀ (Functor.F₀ [ x ,-] u) ) ⊗₀ x ⇒ v
  inner {x} v u = ε.η v ∘ id ⊗₁ ε.η {x} u ∘ α⇒

  VU-UY⇒VY-VU : {U V X Y : Obj} → inner {X} V U ∘ (id ⊗₁ 𝕃 (inner U Y) ∘ α⇒) ⊗₁ id ≈
                          inner V Y ∘ (𝕃 (inner V U) ⊗₁ id) ⊗₁ id
  VU-UY⇒VY-VU {U} {V} {X} {Y} = begin
    inner V U ∘ (id ⊗₁ 𝕃 (inner U Y) ∘ α⇒) ⊗₁ id                       ≈⟨ pushʳ $ ℱ.homomorphism (-⊗ X) ⟩
    (inner V U ∘ (id ⊗₁ 𝕃 (inner U Y)) ⊗₁ id) ∘ α⇒ ⊗₁ id               ≈⟨ pull-last assoc-commute-from ⟩∘⟨refl ⟩
    (ε.η V ∘ id ⊗₁ ε.η U ∘ id ⊗₁ 𝕃 (inner U Y) ⊗₁ id ∘ α⇒) ∘ α⇒ ⊗₁ id  ≈⟨ (∘-resp-≈ʳ $ pullˡ $ ⟺ (ℱ.homomorphism ([ U , V ]₀ ⊗-))) ⟩∘⟨refl ⟩
    (ε.η V ∘ id ⊗₁ (ε.η U ∘ 𝕃 (inner U Y) ⊗₁ id) ∘ α⇒) ∘ α⇒ ⊗₁ id      ≈⟨ ∘-resp-≈ˡ sym-assoc ○ assoc ⟩
    (ε.η V ∘ id ⊗₁ (ε.η U ∘ 𝕃 (inner U Y) ⊗₁ id)) ∘ (α⇒ ∘ α⇒ ⊗₁ id)    ≈⟨ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ ℱ.F-resp-≈ ([ U , V ]₀ ⊗-) (RLadjunct≈id ○ sym-assoc) ⟩
    (ε.η V ∘ id ⊗₁ ((ε.η U ∘ id ⊗₁ ε.η Y) ∘ α⇒)) ∘ (α⇒ ∘ α⇒ ⊗₁ id)     ≈⟨ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ ℱ.homomorphism ([ U , V ]₀ ⊗-) ⟩
    (ε.η V ∘ id ⊗₁ (ε.η U ∘ id ⊗₁ ε.η Y) ∘ id ⊗₁ α⇒) ∘ (α⇒ ∘ α⇒ ⊗₁ id) ≈⟨ pull-last refl ⟩
    ε.η V ∘ id ⊗₁ (ε.η U ∘ id ⊗₁ ε.η Y) ∘ (id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id)   ≈⟨ refl⟩∘⟨ ∘-resp-≈ (ℱ.homomorphism ([ U , V ]₀ ⊗-)) pentagon ⟩
    ε.η V ∘ (id ⊗₁ ε.η U ∘ id ⊗₁ (id ⊗₁ ε.η Y)) ∘ (α⇒ ∘ α⇒)            ≈⟨ sym-assoc ○ sym-assoc ⟩
    ((ε.η V ∘ id ⊗₁ ε.η U ∘ id ⊗₁ (id ⊗₁ ε.η Y)) ∘ α⇒) ∘ α⇒            ≈⟨ pull-last (⟺ assoc-commute-from) ⟩∘⟨refl ⟩
    (ε.η V ∘ id ⊗₁ ε.η U ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ ε.η Y) ∘ α⇒              ≈⟨ assoc ○ ∘-resp-≈ʳ (∘-resp-≈ˡ sym-assoc) ○ ⟺ (center refl) ⟩
    (ε.η V ∘ id ⊗₁ ε.η U ∘ α⇒) ∘ (id ⊗₁ id) ⊗₁ ε.η Y ∘ α⇒              ≈⟨ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ⊗.F-resp-≈ (⊗.identity , refl) ⟩
    (ε.η V ∘ id ⊗₁ ε.η U ∘ α⇒) ∘ id ⊗₁ ε.η Y ∘ α⇒                      ≈˘⟨ center⁻¹ RLadjunct≈id refl ⟩
    ε.η V ∘ (𝕃 (ε.η V ∘ id ⊗₁ ε.η U ∘ α⇒) ⊗₁ id ∘ id ⊗₁ ε.η Y) ∘ α⇒    ≈⟨ ∘-resp-≈ʳ $ pushˡ (⟺ [ ⊗ ]-commute) ⟩
    ε.η V ∘ id ⊗₁ ε.η Y ∘ 𝕃 (inner V U) ⊗₁ id ∘ α⇒                     ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗.F-resp-≈ (refl , ⊗.identity) ⟩∘⟨refl ⟩
    ε.η V ∘ id ⊗₁ ε.η Y ∘ 𝕃 (inner V U) ⊗₁ (id ⊗₁ id) ∘ α⇒             ≈˘⟨ pull-last assoc-commute-from ⟩
    (inner V Y) ∘ (𝕃 (inner V U) ⊗₁ id) ⊗₁ id                          ∎

  expand-[-,-] : {U V X Y : Obj} →
      (ε.η [ X , V ]₀ ∘ id ⊗₁ ε.η [ X , U ]₀ ∘ α⇒) ∘ (L X U V ⊗₁ L X Y U) ⊗₁ id ≈
      𝕃 (ε.η V ∘ id ⊗₁ ε.η Y ∘ α⇒) ∘ 𝕃 (ε.η V ∘ id ⊗₁ ε.η U ∘ α⇒) ⊗₁ id
  expand-[-,-] {U} {V} {X} {Y} = begin
    (inner XV XU) ∘ (L X U V ⊗₁ L X Y U) ⊗₁ id                     ≈⟨ pull-last assoc-commute-from ⟩
    ε.η XV ∘ id ⊗₁ ε.η XU ∘ L X U V ⊗₁ L X Y U ⊗₁ id ∘ α⇒          ≈⟨ refl⟩∘⟨ pullˡ (⟺ ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , refl)) ⟩
    ε.η XV ∘ L X U V ⊗₁ (ε.η XU ∘ L X Y U ⊗₁ id) ∘ α⇒              ≈⟨ refl⟩∘⟨ [ ⊗ ]-decompose₁ ⟩∘⟨refl ⟩
    ε.η XV ∘ (L X U V ⊗₁ id ∘ id ⊗₁ (ε.η XU ∘ L X Y U ⊗₁ id)) ∘ α⇒ ≈⟨ center⁻¹ RLadjunct≈id (∘-resp-≈ˡ (ℱ.F-resp-≈ ([ U , V ]₀ ⊗-) RLadjunct≈id)) ⟩
    𝕃 (inner V U) ∘ (id ⊗₁ 𝕃 (inner U Y) ∘ α⇒)                     ≈˘⟨ 𝕃-comm′ ⟩
    𝕃 (inner V U ∘ (id ⊗₁ 𝕃 (inner U Y) ∘ α⇒) ⊗₁ id)               ≈⟨ 𝕃-resp-≈ VU-UY⇒VY-VU ⟩
    𝕃 (inner V Y ∘ (𝕃 (inner V U) ⊗₁ id) ⊗₁ id)                    ≈⟨ 𝕃-comm′ ⟩
    𝕃 (inner V Y) ∘ 𝕃 (inner V U) ⊗₁ id                            ∎
    where
    XV = [ X , V ]₀
    XU = [ X , U ]₀
    UV = [ U , V ]₀

pentagon′ : {U V X Y : Obj} →
            [ [ U , V ]₀ ⇒ [ [ Y , U ]₀ , [ [ X , Y ]₀ , [ X , V ]₀ ]₀ ]₀ ]⟨
             L X U V                            ⇒⟨ [ [ X , U ]₀ , [ X , V ]₀ ]₀ ⟩
             L [ X , Y ]₀ [ X , U ]₀ [ X , V ]₀ ⇒⟨ [ [ [ X , Y ]₀ , [ X , U ]₀ ]₀ , [ [ X , Y ]₀ , [ X , V ]₀ ]₀ ]₀ ⟩
             [ L X Y U , id ]₁
           ≈ L Y U V                            ⇒⟨ [ [ Y , U ]₀ , [ Y , V ]₀ ]₀ ⟩
             [ id , L X Y V ]₁
           ⟩
pentagon′ {U} {V} {X} {Y} = begin
  [ L X Y U , id ]₁ ∘ L [ X , Y ]₀ XU XV ∘ L X U V                             ≈˘⟨ refl ⟩∘⟨ 𝕃-comm′ ⟩
  [ L X Y U , id ]₁ ∘ 𝕃 (𝕃 (ε.η XV ∘ id ⊗₁ ε.η XU ∘ α⇒) ∘ L X U V ⊗₁ id)       ≈˘⟨ pushˡ [ [-,-] ]-commute ⟩
  ([ id , 𝕃 (inner XV XU) ∘ L X U V ⊗₁ id ]₁ ∘ [ L X Y U , id ]₁) ∘ η.η UV     ≈˘⟨ pushʳ (mate.commute₁ (L X Y U)) ⟩
  [ id , 𝕃 (inner XV XU) ∘ L X U V ⊗₁ id ]₁ ∘ [ id , id ⊗₁ L X Y U ]₁ ∘ η.η UV ≈˘⟨ pushˡ (ℱ.homomorphism [ [ Y , U ]₀ ,-]) ⟩
  𝕃 ((𝕃 (inner XV XU) ∘ L X U V ⊗₁ id) ∘ id ⊗₁ L X Y U)                        ≈˘⟨ 𝕃-resp-≈ $ pushʳ [ ⊗ ]-decompose₁ ⟩
  𝕃 (𝕃 (inner XV XU) ∘ L X U V ⊗₁ L X Y U)                                     ≈˘⟨ 𝕃-resp-≈ $ 𝕃-comm′ ⟩
  𝕃 (𝕃 $ (inner XV XU) ∘ (L X U V ⊗₁ L X Y U) ⊗₁ id)                           ≈⟨ 𝕃-resp-≈ $ 𝕃-resp-≈ $ expand-[-,-] ⟩
  𝕃 (𝕃 $ 𝕃 (inner V Y) ∘ 𝕃 (inner V U) ⊗₁ id)                                  ≈⟨ 𝕃-resp-≈ 𝕃-comm′ ⟩
  𝕃 (L X Y V ∘ 𝕃 (inner V U))                                                  ≈⟨ pushˡ (ℱ.homomorphism [ [ Y , U ]₀ ,-]) ⟩
  [ id , L X Y V ]₁ ∘ L Y U V                                                  ∎
  where
  XV = [ X , V ]₀
  XU = [ X , U ]₀
  UV = [ U , V ]₀
