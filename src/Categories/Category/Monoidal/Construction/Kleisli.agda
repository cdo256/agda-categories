{-# OPTIONS --cubical-compatible --without-K --safe #-}
module Categories.Category.Monoidal.Construction.Kleisli where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (Strength; RightStrength)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Commutative.Properties using (module CommutativeProperties; module SymmetricProperties)
open import Categories.Category.Construction.Kleisli using (Kleisli; module TripleNotation)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Functor.Bifunctor using (Bifunctor)


import Categories.Morphism as MC
import Categories.Morphism.Reasoning as MR
import Categories.Monad.Strong.Properties as StrongProps
import Categories.Category.Monoidal.Utilities as MonoidalUtils

private
  variable
    o ℓ e : Level

-- The Kleisli category of a commutative monad (where 𝒞 is symmetric) is monoidal.

module _ {𝒞 : Category o ℓ e} {monoidal : Monoidal 𝒞} (symmetric : Symmetric monoidal) (CM : CommutativeMonad (Symmetric.braided symmetric)) where
  open Category 𝒞
  open MR 𝒞
  open HomReasoning
  open Equiv

  open CommutativeMonad CM hiding (identityˡ)
  open Monad M using (μ)
  open TripleNotation M

  open StrongProps.Left.Shorthands strength
  open StrongProps.Right.Shorthands rightStrength
  open MonoidalUtils.Shorthands monoidal using (α⇒; α⇐; λ⇒; λ⇐; ρ⇒; ρ⇐)


  open Symmetric symmetric
  open CommutativeProperties braided CM
  open SymmetricProperties symmetric CM

  open MC (Kleisli M) using (_≅_)

  ⊗' : Bifunctor (Kleisli M) (Kleisli M) (Kleisli M)
  ⊗' = record
    { F₀ = λ (X , Y) → X ⊗₀ Y
    ; F₁ = λ (f , g) → ψ ∘ (f ⊗₁ g)
    ; identity = identity'
    ; homomorphism = λ {(X₁ , X₂)} {(Y₁ , Y₂)} {(Z₁ , Z₂)} {(f , g)} {(h , i)} → homomorphism' {X₁} {X₂} {Y₁} {Y₂} {Z₁} {Z₂} {f} {g} {h} {i}
    ; F-resp-≈ = λ (f≈g , h≈i) → ∘-resp-≈ʳ (⊗.F-resp-≈ (f≈g , h≈i))
    }
    where
    identity' : ∀ {X} {Y} → ψ ∘ (η {X} ⊗₁ η {Y}) ≈ η
    identity' = begin
      (τ * ∘ σ) ∘ (η ⊗₁ η)              ≈˘⟨ refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ⟩
      (τ * ∘ σ) ∘ (id ⊗₁ η) ∘ (η ⊗₁ id) ≈⟨ pullʳ (pullˡ η-comm) ⟩
      τ * ∘ η ∘ (η ⊗₁ id)               ≈⟨ pullˡ *-identityʳ ⟩
      τ ∘ (η ⊗₁ id)                     ≈⟨ RightStrength.η-comm rightStrength ⟩
      η                                 ∎
    homomorphism' : ∀ {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Obj} {f : X₁ ⇒ M.F.₀ Y₁} {g : X₂ ⇒ M.F.₀ Y₂} {h : Y₁ ⇒ M.F.₀ Z₁} {i : Y₂ ⇒ M.F.₀ Z₂} → ψ ∘ ((h * ∘ f) ⊗₁ (i * ∘ g)) ≈ (ψ ∘ (h ⊗₁ i)) * ∘ ψ ∘ (f ⊗₁ g)
    homomorphism' {f = f} {g} {h} {i} = begin
      ψ ∘ ((h * ∘ f) ⊗₁ (i * ∘ g))                           ≈˘⟨ refl⟩∘⟨ (pullˡ (sym ⊗.homomorphism) ○ sym ⊗.homomorphism) ⟩
      ψ ∘ (μ.η _ ⊗₁ μ.η _) ∘ (M.F.₁ h ⊗₁ M.F.₁ i) ∘ (f ⊗₁ g) ≈˘⟨ extendʳ ψ-μ ⟩
      ψ * ∘ ψ ∘ (M.F.₁ h ⊗₁ M.F.₁ i) ∘ (f ⊗₁ g)              ≈⟨ refl⟩∘⟨ extendʳ ψ-comm ⟩
      ψ * ∘ M.F.₁ (h ⊗₁ i) ∘ ψ ∘ (f ⊗₁ g)                    ≈⟨ pullˡ *∘F₁ ⟩
      (ψ ∘ (h ⊗₁ i)) * ∘ ψ ∘ (f ⊗₁ g)                        ∎

  unitorˡ' : ∀ {X} → unit ⊗₀ X ≅ X
  unitorˡ' = record { from = η ∘ λ⇒ ; to = η ∘ λ⇐ ; iso = record
    { isoˡ = pullˡ *-identityʳ ○ cancelʳ unitorˡ.isoˡ
    ; isoʳ = pullˡ *-identityʳ ○ cancelʳ unitorˡ.isoʳ
    } }

  unitorʳ' : ∀ {X} → X ⊗₀ unit ≅ X
  unitorʳ' = record { from = η ∘ ρ⇒ ; to = η ∘ ρ⇐ ; iso = record
    { isoˡ = pullˡ *-identityʳ ○ cancelʳ unitorʳ.isoˡ
    ; isoʳ = pullˡ *-identityʳ ○ cancelʳ unitorʳ.isoʳ
    } }

  associator' : ∀ {X Y Z} → (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)
  associator' = record { from = η ∘ α⇒ ; to = η ∘ α⇐ ; iso = record
    { isoˡ = pullˡ *-identityʳ ○ cancelʳ associator.isoˡ
    ; isoʳ = pullˡ *-identityʳ ○ cancelʳ associator.isoʳ
    } }

  Kleisli-Monoidal : Monoidal (Kleisli M)
  Kleisli-Monoidal = record
    { ⊗ = ⊗'
    ; unit = unit
    ; unitorˡ = unitorˡ'
    ; unitorʳ = unitorʳ'
    ; associator = associator'
    ; unitorˡ-commute-from = unitorˡ-commute-from'
    ; unitorˡ-commute-to = unitorˡ-commute-to'
    ; unitorʳ-commute-from = unitorʳ-commute-from'
    ; unitorʳ-commute-to = unitorʳ-commute-to'
    ; assoc-commute-from = assoc-commute-from'
    ; assoc-commute-to = assoc-commute-to'
    ; triangle = triangle'
    ; pentagon = pentagon'
    }
    where
    unitorˡ-commute-from' : ∀ {X} {Y} {f : X ⇒ M.F.₀ Y} → (η ∘ λ⇒) * ∘ ψ ∘ (η ⊗₁ f) ≈ f * ∘ η ∘ λ⇒
    unitorˡ-commute-from' {f = f} = begin 
      (η ∘ λ⇒) * ∘ ψ ∘ (η ⊗₁ f) ≈⟨ *⇒F₁ ⟩∘⟨ ψ-σ' ⟩ 
      M.F.₁ λ⇒ ∘ σ ∘ (id ⊗₁ f)  ≈⟨ pullˡ (Strength.identityˡ strength) ⟩ 
      λ⇒ ∘ (id ⊗₁ f)            ≈⟨ unitorˡ-commute-from ⟩ 
      f ∘ λ⇒                    ≈˘⟨ pullˡ *-identityʳ ⟩ 
      f * ∘ η ∘ λ⇒              ∎
    unitorˡ-commute-to' : ∀ {X} {Y} {f : X ⇒ M.F.₀ Y} → (η ∘ λ⇐) * ∘ f ≈ (ψ ∘ (η ⊗₁ f)) * ∘ η ∘ λ⇐
    unitorˡ-commute-to' {f = f} = begin 
      (η ∘ λ⇐) * ∘ f                     ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ λ⇐ ∘ f                       ≈˘⟨ refl⟩∘⟨ (cancelˡ unitorˡ.isoʳ) ⟩ 
      M.F.₁ λ⇐ ∘ λ⇒ ∘ λ⇐ ∘ f             ≈˘⟨ pullʳ (pullˡ (Strength.identityˡ strength)) ⟩
      (M.F.₁ λ⇐ ∘ M.F.₁ λ⇒) ∘ σ ∘ λ⇐ ∘ f ≈⟨ elimˡ (sym M.F.homomorphism ○ (M.F.F-resp-≈ unitorˡ.isoˡ ○ M.F.identity)) ⟩
      σ ∘ λ⇐ ∘ f                         ≈˘⟨ pullʳ (sym unitorˡ-commute-to) ⟩ 
      (σ ∘ (id ⊗₁ f)) ∘ λ⇐               ≈˘⟨ ψ-σ' ⟩∘⟨refl ⟩ 
      (ψ ∘ (η ⊗₁ f)) ∘ λ⇐                ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (η ⊗₁ f)) * ∘ η ∘ λ⇐          ∎
    unitorʳ-commute-from' : ∀ {X} {Y} {f : X ⇒ M.F.₀ Y} → (η ∘ ρ⇒) * ∘ ψ ∘ (f ⊗₁ η) ≈ f * ∘ η ∘ ρ⇒
    unitorʳ-commute-from' {f = f} = begin 
      (η ∘ ρ⇒) * ∘ ψ ∘ (f ⊗₁ η) ≈⟨ *⇒F₁ ⟩∘⟨ ψ-τ' ⟩ 
      M.F.₁ ρ⇒ ∘ τ ∘ (f ⊗₁ id)  ≈⟨ pullˡ (RightStrength.identityˡ rightStrength) ⟩ 
      ρ⇒ ∘ (f ⊗₁ id)            ≈⟨ unitorʳ-commute-from ⟩ 
      f ∘ ρ⇒                    ≈˘⟨ pullˡ *-identityʳ ⟩ 
      f * ∘ η ∘ ρ⇒              ∎
    unitorʳ-commute-to' : ∀ {X} {Y} {f : X ⇒ M.F.₀ Y} → (η ∘ ρ⇐) * ∘ f ≈ (ψ ∘ (f ⊗₁ η)) * ∘ η ∘ ρ⇐
    unitorʳ-commute-to' {f = f} = begin 
      (η ∘ ρ⇐) * ∘ f                     ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ ρ⇐ ∘ f                       ≈˘⟨ refl⟩∘⟨ (cancelˡ unitorʳ.isoʳ) ⟩ 
      M.F.₁ ρ⇐ ∘ ρ⇒ ∘ ρ⇐ ∘ f             ≈˘⟨ pullʳ (pullˡ (RightStrength.identityˡ rightStrength)) ⟩
      (M.F.₁ ρ⇐ ∘ M.F.₁ ρ⇒) ∘ τ ∘ ρ⇐ ∘ f ≈⟨ elimˡ (sym M.F.homomorphism ○ (M.F.F-resp-≈ unitorʳ.isoˡ ○ M.F.identity)) ⟩
      τ ∘ ρ⇐ ∘ f                         ≈˘⟨ pullʳ (sym unitorʳ-commute-to) ⟩ 
      (τ ∘ (f ⊗₁ id)) ∘ ρ⇐               ≈˘⟨ ψ-τ' ⟩∘⟨refl ⟩ 
      (ψ ∘ (f ⊗₁ η)) ∘ ρ⇐                ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (f ⊗₁ η)) * ∘ η ∘ ρ⇐          ∎
    assoc-commute-from' : ∀ {X Y} {f : X ⇒ M.F.₀ Y} {A B} {g : A ⇒ M.F.₀ B} {U V} {h : U ⇒ M.F.₀ V} → (η ∘ α⇒) * ∘ ψ ∘ ((ψ ∘ (f ⊗₁ g)) ⊗₁ h) ≈ (ψ ∘ (f ⊗₁ (ψ ∘ (g ⊗₁ h)))) * ∘ (η ∘ α⇒)
    assoc-commute-from' {f = f} {g = g} {h = h} = begin  
      (η ∘ α⇒) * ∘ ψ ∘ ((ψ ∘ (f ⊗₁ g)) ⊗₁ h)     ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ α⇒ ∘ ψ ∘ ((ψ ∘ (f ⊗₁ g)) ⊗₁ h)       ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityˡ)) ⟩ 
      M.F.₁ α⇒ ∘ ψ ∘ (ψ ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ h) ≈⟨ (sym-assoc ○ pullˡ (assoc ○ ψ-assoc-from) ○ assoc²βε) ⟩ 
      ψ ∘ (id ⊗₁ ψ) ∘ α⇒ ∘ ((f ⊗₁ g) ⊗₁ h)       ≈˘⟨ pullʳ (pullʳ (sym assoc-commute-from)) ⟩ 
      (ψ ∘ (id ⊗₁ ψ) ∘ (f ⊗₁ (g ⊗₁ h))) ∘ α⇒     ≈⟨ (refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , refl))) ⟩∘⟨refl ⟩ 
      (ψ ∘ (f ⊗₁ (ψ ∘ (g ⊗₁ h)))) ∘ α⇒           ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (f ⊗₁ (ψ ∘ (g ⊗₁ h)))) * ∘ (η ∘ α⇒)   ∎
    assoc-commute-to' : ∀ {X Y} {f : X ⇒ M.F.₀ Y} {A B} {g : A ⇒ M.F.₀ B} {U V} {h : U ⇒ M.F.₀ V} → (η ∘ α⇐) * ∘ ψ ∘ (f ⊗₁ (ψ ∘ (g ⊗₁ h))) ≈ (ψ ∘ ((ψ ∘ (f ⊗₁ g)) ⊗₁ h)) * ∘ (η ∘ α⇐)
    assoc-commute-to' {f = f} {g = g} {h = h} = begin 
      (η ∘ α⇐) * ∘ ψ ∘ (f ⊗₁ (ψ ∘ (g ⊗₁ h)))     ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ α⇐ ∘ ψ ∘ (f ⊗₁ (ψ ∘ (g ⊗₁ h)))       ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , refl)) ⟩ 
      M.F.₁ α⇐ ∘ ψ ∘ (id ⊗₁ ψ) ∘ (f ⊗₁ (g ⊗₁ h)) ≈⟨ (sym-assoc ○ (pullˡ (assoc ○ ψ-assoc-to) ○ assoc²βε)) ⟩ 
      ψ ∘ (ψ ⊗₁ id) ∘ α⇐ ∘ (f ⊗₁ (g ⊗₁ h))       ≈˘⟨ pullʳ (pullʳ (sym assoc-commute-to)) ⟩
      (ψ ∘ (ψ ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ h)) ∘ α⇐     ≈⟨ (refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityˡ))) ⟩∘⟨refl ⟩ 
      (ψ ∘ ((ψ ∘ (f ⊗₁ g)) ⊗₁ h)) ∘ α⇐           ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ ((ψ ∘ (f ⊗₁ g)) ⊗₁ h)) * ∘ (η ∘ α⇐)   ∎
    triangle' : ∀ {X} {Y} → (ψ ∘ (η {X} ⊗₁ (η ∘ λ⇒))) * ∘ (η ∘ α⇒) ≈ ψ ∘ ((η ∘ ρ⇒) ⊗₁ η {Y})
    triangle' = begin 
      (ψ ∘ (η ⊗₁ (η ∘ λ⇒))) * ∘ (η ∘ α⇒) ≈⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ λ⇒))) ∘ α⇒         ≈˘⟨ pullˡ (pullʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , refl))) ⟩ 
      (ψ ∘ (η ⊗₁ η)) ∘ (id ⊗₁ λ⇒) ∘ α⇒   ≈⟨ (refl⟩∘⟨ triangle) ⟩ 
      (ψ ∘ (η ⊗₁ η)) ∘ (ρ⇒ ⊗₁ id)        ≈⟨ pullʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityʳ)) ⟩  
      ψ ∘ ((η ∘ ρ⇒) ⊗₁ η)                ∎
    pentagon' : ∀ {A B C D : Obj} → (ψ {A} {B ⊗₀ (C ⊗₀ D)} ∘ (η ⊗₁ (η ∘ α⇒))) * ∘ (η ∘ α⇒) * ∘ (ψ ∘ ((η ∘ α⇒) ⊗₁ η)) ≈ (η ∘ α⇒) * ∘ (η ∘ α⇒)
    pentagon' = begin 
      (ψ ∘ (η ⊗₁ (η ∘ α⇒))) * ∘ (η ∘ α⇒) * ∘ (ψ ∘ ((η ∘ α⇒) ⊗₁ η)) 
        ≈⟨ refl⟩∘⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ α⇒))) * ∘ M.F.₁ α⇒ ∘ (ψ ∘ ((η ∘ α⇒) ⊗₁ η))   
        ≈⟨ pullˡ (*∘F₁ ○ *-resp-≈ assoc) ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ α⇒)) ∘ α⇒) * ∘ (ψ ∘ ((η ∘ α⇒) ⊗₁ η))         
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityʳ)) ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ α⇒)) ∘ α⇒) * ∘ (ψ ∘ (η ⊗₁ η) ∘ (α⇒ ⊗₁ id))  
        ≈⟨ refl⟩∘⟨ pullˡ ψ-η ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ α⇒)) ∘ α⇒) * ∘ (η ∘ (α⇒ ⊗₁ id))            
        ≈⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ α⇒)) ∘ α⇒) ∘ (α⇒ ⊗₁ id)                    
        ≈˘⟨ sym-assoc ○ (∘-resp-≈ʳ sym-assoc ○ pullˡ (pullʳ (pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , refl))))) ⟩ 
      ψ ∘ (η ⊗₁ η) ∘ (id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id)                 
        ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ pentagon) ⟩ 
      ψ ∘ (η ⊗₁ η) ∘ (α⇒ ∘ α⇒)                                               
        ≈⟨ (pullˡ ψ-η) ○ sym-assoc ⟩ 
      (η ∘ α⇒) ∘ α⇒                                                         
        ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (η ∘ α⇒) * ∘ (η ∘ α⇒)                                                 
        ∎
