{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Fibration.Base
open import Categories.Functor
open import Categories.Morphism.Cartesian using (Cartesian)
open import Data.Product using (_,_)
open import Function.Bundles using (Func; _⟨$⟩_)

module Categories.Fibration.FamilyFibration {o ℓ e}
  (C : Category o ℓ e)
  ℓI ℓI'
  where

open import Categories.Morphism (Setoids ℓI ℓI') using () renaming (_≅_ to _≅S_; module ≅ to ≅S)
open import Categories.Morphism C using (_≅_)
open import Categories.Category.Construction.SetoidIndexedFamily C as SIF

open import Level

open import Relation.Binary.Bundles using (Setoid)

private
  module C = Category C
  FamC : Category
    (suc (o ⊔ ℓ ⊔ e ⊔ ℓI ⊔ ℓI'))
    (o ⊔ ℓ ⊔ e ⊔ ℓI ⊔ ℓI')
    (o ⊔ ℓ ⊔ e ⊔ ℓI ⊔ ℓI')
  FamC = CategoryOfFamilies ℓI ℓI'
  S* = Setoids ℓI ℓI'
  module S* = Category S*
  module FamC = Category FamC

open C.HomReasoning

U₀ : FamC.Obj → S*.Obj
U₀ A = A.I
  where
  module A = Family A

U₁ : ∀ {A B} → FamC [ A , B ] → S* [ U₀ A , U₀ B ]
U₁ f = f.u
  where
  module f = SIF.Hom f

U : Functor FamC S*
U = record
  { F₀ = U₀
  ; F₁ = U₁
  ; identity = λ {A} {x} → Setoid.refl (U₀ A)
  ; homomorphism = λ {X} {Y} {Z} {f} {g} {x} → Setoid.refl (U₀ Z)
  ; F-resp-≈ = SIF._≈_.u≈
  }

open Fibration
liftX : ∀ (I : S*.Obj) (Y : FamC.Obj) → S* [ I , U₀ Y ] → FamC.Obj
Family.I (liftX I₀ Y₀ u) = I₀
Family.X (liftX I₀ Y₀ u) i = Y.X (u ⟨$⟩ i)
  where
  module Y = Family Y₀
  module u = Func u
Family.resp (liftX I₀ Y₀ u) p = Y.resp (u.cong p)
  where
  module Y = Family Y₀
  module u = Func u
Family.resp-refl (liftX I₀ Y₀ u) =
  C.Equiv.trans (Y.resp-irr (u.cong I.refl) Y.refl) Y.resp-refl
  where
  module I = Setoid I₀
  module Y = Family Y₀
  module u = Func u
Family.resp-sym (liftX I₀ Y₀ u) p =
  C.Equiv.trans
    (Y.resp-irr (u.cong (I.sym p)) (Y.sym (u.cong p)))
    (Y.resp-sym (u.cong p))
  where
  module I = Setoid I₀
  module Y = Family Y₀
  module u = Func u
Family.resp-trans (liftX I₀ Y₀ u) p q =
  C.Equiv.trans
    (Y.resp-irr (u.cong (I.trans p q)) (Y.trans (u.cong p) (u.cong q)))
    (Y.resp-trans (u.cong p) (u.cong q))
  where
  module I = Setoid I₀
  module Y = Family Y₀
  module u = Func u
Family.resp-irr (liftX I₀ Y₀ u) p q = Y.resp-irr (u.cong p) (u.cong q)
  where
  module Y = Family Y₀
  module u = Func u

liftf : ∀ {I Y} (u : S* [ I , U₀ Y ]) → FamC [ liftX I Y u , Y ]
Hom.u (liftf u) = u
Hom.f (liftf u) _ = C.id
Hom.coh (liftf u) _ = C.Equiv.trans C.identityʳ (C.Equiv.sym C.identityˡ)

liftφ : ∀ {I Y} (u : S* [ I , U₀ Y ]) → U₀ (liftX I Y u) ≅S I
liftφ u = ≅S.refl

lift-u∘φ⁻≈pf : ∀ {I Y} (u : S* [ I , U₀ Y ]) → S* [ u S*.∘ _≅S_.from (liftφ {I} {Y} u) ≈ U₁ (liftf {I} {Y} u) ]
lift-u∘φ⁻≈pf {Y = Y₀} u {x} = Setoid.refl (U₀ Y₀)

lift-cartesian : ∀ {I Y} (u : S* [ I , U₀ Y ]) → Cartesian U (liftf {Y = Y} u)
lift-cartesian {I = I₀} {Y = Y₀} u = record
    { universal = λ {A} {v} h eq → universal v h eq
    ; commute = λ {A} {v} {h} eq → universal-commute v h eq
    ; compat = λ {A} {v} {h} eq {x} → SI.refl
    }
  where
  module SI = Setoid I₀
  module Y = Family Y₀
  module u = Func u

  universal : ∀ {A} (v : S* [ U₀ A , I₀ ])
      (h : FamC [ A , Y₀ ])
      (eq : S* [ u S*.∘ v ≈ U₁ h ])
      → FamC [ A , liftX I₀ Y₀ u ]
  Hom.u (universal v h eq) = v
  Hom.f (universal v h eq) i = Y.resp.from (Y.sym (eq {i})) C.∘ SIF.Hom.f h i
  Hom.coh (universal {A} v h eq) {i} {j} p = begin
      Xu.resp.from (v.cong p) C.∘ (Y.resp.from (Y.sym (eq {i})) C.∘ SIF.Hom.f h i)
        ≈⟨ C.sym-assoc ⟩
      (Xu.resp.from (v.cong p) C.∘ Y.resp.from (Y.sym (eq {i}))) C.∘ SIF.Hom.f h i
        ≈⟨ C.∘-resp-≈ˡ (C.Equiv.sym (Y.resp-trans (Y.sym (eq {i})) (u.cong (v.cong p)))) ⟩
      Y.resp.from (Y.trans (Y.sym (eq {i})) (u.cong (v.cong p))) C.∘ SIF.Hom.f h i
        ≈⟨ C.∘-resp-≈ˡ (Y.resp-irr (Y.trans (Y.sym (eq {i})) (u.cong (v.cong p))) (Y.trans (SIF.Hom.u.cong h p) (Y.sym (eq {j})))) ⟩
      Y.resp.from (Y.trans (SIF.Hom.u.cong h p) (Y.sym (eq {j}))) C.∘ SIF.Hom.f h i
        ≈⟨ C.∘-resp-≈ˡ (Y.resp-trans (SIF.Hom.u.cong h p) (Y.sym (eq {j}))) ⟩
      (Y.resp.from (Y.sym (eq {j})) C.∘ Y.resp.from (SIF.Hom.u.cong h p)) C.∘ SIF.Hom.f h i
        ≈⟨ C.assoc ⟩
      Y.resp.from (Y.sym (eq {j})) C.∘ (Y.resp.from (SIF.Hom.u.cong h p) C.∘ SIF.Hom.f h i)
        ≈⟨ refl⟩∘⟨ SIF.Hom.coh h p ⟩
      Y.resp.from (Y.sym (eq {j})) C.∘ (SIF.Hom.f h j C.∘ A.resp.from p)
        ≈⟨ C.sym-assoc ⟩
      (Y.resp.from (Y.sym (eq {j})) C.∘ SIF.Hom.f h j) C.∘ A.resp.from p
        ∎
    where
    module A = Family A
    module Xu = Family (liftX I₀ Y₀ u)
    module v = Func v

  universal-commute : ∀ {A} (v : S* [ U₀ A , I₀ ])
      (h : FamC [ A , Y₀ ])
      (eq : S* [ u S*.∘ v ≈ U₁ h ])
      → FamC [ liftf u FamC.∘ universal v h eq ≈ h ]
  _≈_.u≈ (universal-commute v h eq) = eq
  _≈_.f≈ (universal-commute v h eq) {i} = begin
      Y.resp.from (eq {i}) C.∘ (C.id C.∘ (Y.resp.from (Y.sym (eq {i})) C.∘ SIF.Hom.f h i))
        ≈⟨ C.∘-resp-≈ʳ C.identityˡ ⟩
      Y.resp.from (eq {i}) C.∘ (Y.resp.from (Y.sym (eq {i})) C.∘ SIF.Hom.f h i)
        ≈⟨ C.sym-assoc ⟩
      (Y.resp.from (eq {i}) C.∘ Y.resp.from (Y.sym (eq {i}))) C.∘ SIF.Hom.f h i
        ≈⟨ C.∘-resp-≈ˡ (C.Equiv.trans (Y.resp-irr (eq {i}) (Y.sym (Y.sym (eq {i})))) (Y.resp-sym (Y.sym (eq {i})))) ⟩∘⟨refl ⟩
      (Y.resp.to (Y.sym (eq {i})) C.∘ Y.resp.from (Y.sym (eq {i}))) C.∘ SIF.Hom.f h i
        ≈⟨ Y.resp.isoˡ (Y.sym (eq {i})) ⟩∘⟨refl ⟩
      C.id C.∘ SIF.Hom.f h i
        ≈⟨ C.identityˡ ⟩
      SIF.Hom.f h i
      ∎

FamilyFibration : Fibration U
FamilyFibration .X {I} {Y} u = liftX I Y u
FamilyFibration .f {I} {Y} u = liftf {I} {Y} u
FamilyFibration .φ {I} {Y} u = liftφ {I} {Y} u
FamilyFibration .u∘φ⁻≈pf {I} {Y} u = lift-u∘φ⁻≈pf {I} {Y} u
FamilyFibration .cartesian {I} {Y} u = lift-cartesian {I} {Y} u
