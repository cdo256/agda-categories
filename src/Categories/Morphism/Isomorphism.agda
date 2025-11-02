{-# OPTIONS --cubical-compatible --without-K --safe #-}
open import Categories.Category

-- Mainly *properties* of isomorphisms, and a lot of other things too

-- TODO: split things up more semantically?

module Categories.Morphism.Isomorphism {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (_⊔_)
open import Function using (flip)

open import Data.Product using (_,_)
open import Relation.Binary using (Rel; _Preserves_⟶_; IsEquivalence)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

import Categories.Category.Construction.Core as Core
open import Categories.Category.Groupoid using (IsGroupoid)
import Categories.Category.Groupoid.Properties as GroupoidProps
import Categories.Morphism as Morphism
import Categories.Morphism.Properties as MorphismProps
import Categories.Morphism.IsoEquiv as IsoEquiv
import Categories.Category.Construction.Path as Path

open Core 𝒞 using (Core; Core-isGroupoid; CoreGroupoid; module Shorthands)
open Morphism 𝒞
open MorphismProps 𝒞
open Path 𝒞

import Categories.Morphism.Reasoning as MR

open Category 𝒞
open Definitions 𝒞

private
  module MCore where
    open GroupoidProps CoreGroupoid public
    open MorphismProps Core         public
    open Morphism      Core         public
    open Path          Core         public

  variable
    A B C D E F : Obj

open Shorthands hiding (_≅_)

CommutativeIso = IsGroupoid.CommutativeSquare Core-isGroupoid

--------------------
-- Also stuff about transitive closure

∘ᵢ-tc : A [ _≅_ ]⁺ B → A ≅ B
∘ᵢ-tc = MCore.∘-tc

infix 4 _≃⁺_
_≃⁺_ : Rel (A [ _≅_ ]⁺ B) e
_≃⁺_ = MCore._≈⁺_

TransitiveClosure : Category o (o ⊔ ℓ ⊔ e) e
TransitiveClosure = MCore.Path

--------------------
-- some infrastructure setup in order to say something about morphisms and isomorphisms
module _ where
  private
    data IsoPlus : A [ _⇒_ ]⁺ B → Set (o ⊔ ℓ ⊔ e) where
      [_]     : {f : A ⇒ B} {g : B ⇒ A} → Iso f g → IsoPlus [ f ]
      _∼⁺⟨_⟩_ : ∀ A {f⁺ : A [ _⇒_ ]⁺ B} {g⁺ : B [ _⇒_ ]⁺ C} → IsoPlus f⁺ → IsoPlus g⁺ → IsoPlus (_ ∼⁺⟨ f⁺ ⟩ g⁺)

  open _≅_

  ≅⁺⇒⇒⁺ : A [ _≅_ ]⁺ B → A [ _⇒_ ]⁺ B
  ≅⁺⇒⇒⁺ [ f ]            = [ from f ]
  ≅⁺⇒⇒⁺ (_ ∼⁺⟨ f⁺ ⟩ f⁺′) = _ ∼⁺⟨ ≅⁺⇒⇒⁺ f⁺ ⟩ ≅⁺⇒⇒⁺ f⁺′

  reverse : A [ _≅_ ]⁺ B → B [ _≅_ ]⁺ A
  reverse [ f ]            = [ ≅.sym f ]
  reverse (_ ∼⁺⟨ f⁺ ⟩ f⁺′) = _ ∼⁺⟨ reverse f⁺′ ⟩ reverse f⁺

  reverse⇒≅-sym : (f⁺ : A [ _≅_ ]⁺ B) → ∘ᵢ-tc (reverse f⁺) ≡ ≅.sym (∘ᵢ-tc f⁺)
  reverse⇒≅-sym [ f ]            = ≡.refl
  reverse⇒≅-sym (_ ∼⁺⟨ f⁺ ⟩ f⁺′)  = ≡.cong₂ (Morphism.≅.trans 𝒞) (reverse⇒≅-sym f⁺′) (reverse⇒≅-sym f⁺)

  TransitiveClosure-groupoid : IsGroupoid TransitiveClosure
  TransitiveClosure-groupoid = record
    { _⁻¹ = reverse
    ; iso = λ {_ _ f⁺} → record { isoˡ = isoˡ′ f⁺ ; isoʳ = isoʳ′ f⁺ }
    }
    where
      open HomReasoningᵢ

      isoˡ′ : (f⁺ : A [ _≅_ ]⁺ B) → ∘ᵢ-tc (reverse f⁺) ∘ᵢ ∘ᵢ-tc f⁺ ≈ᵢ ≅.refl
      isoˡ′ f⁺ = begin
          ∘ᵢ-tc (reverse f⁺) ∘ᵢ ∘ᵢ-tc f⁺
        ≡⟨ ≡.cong (_∘ᵢ ∘ᵢ-tc f⁺) (reverse⇒≅-sym f⁺) ⟩
          ≅.sym (∘ᵢ-tc f⁺) ∘ᵢ ∘ᵢ-tc f⁺
        ≈⟨ ⁻¹-iso.isoˡ ⟩
          ≅.refl
        ∎

      isoʳ′ : (f⁺ : A [ _≅_ ]⁺ B) → ∘ᵢ-tc f⁺ ∘ᵢ ∘ᵢ-tc (reverse f⁺) ≈ᵢ ≅.refl
      isoʳ′ f⁺ = begin
          ∘ᵢ-tc f⁺ ∘ᵢ ∘ᵢ-tc (reverse f⁺)
        ≡⟨ ≡.cong (∘ᵢ-tc f⁺ ∘ᵢ_) (reverse⇒≅-sym f⁺) ⟩
          ∘ᵢ-tc f⁺ ∘ᵢ ≅.sym (∘ᵢ-tc f⁺)
        ≈⟨ ⁻¹-iso.isoʳ ⟩
          ≅.refl
        ∎

  from-∘ᵢ-tc : (f⁺ : A [ _≅_ ]⁺ B) → from (∘ᵢ-tc f⁺) ≡ ∘-tc (≅⁺⇒⇒⁺ f⁺)
  from-∘ᵢ-tc [ f ]            = ≡.refl
  from-∘ᵢ-tc (_ ∼⁺⟨ f⁺ ⟩ f⁺′) = ≡.cong₂ _∘_ (from-∘ᵢ-tc f⁺′) (from-∘ᵢ-tc f⁺)

  ≅*⇒⇒*-cong : ≅⁺⇒⇒⁺ {A} {B} Preserves _≃⁺_ ⟶ _≈⁺_
  ≅*⇒⇒*-cong {_} {_} {f⁺} {g⁺} f⁺≃⁺g⁺ = begin
    ∘-tc (≅⁺⇒⇒⁺ f⁺)  ≡˘⟨ from-∘ᵢ-tc f⁺ ⟩
    from (∘ᵢ-tc f⁺)  ≈⟨ from-≈ f⁺≃⁺g⁺ ⟩
    from (∘ᵢ-tc g⁺)  ≡⟨ from-∘ᵢ-tc g⁺ ⟩
    ∘-tc (≅⁺⇒⇒⁺ g⁺)  ∎
    where open HomReasoning

  ≅-shift : ∀ {f⁺ : A [ _≅_ ]⁺ B} {g⁺ : B [ _≅_ ]⁺ C} {h⁺ : A [ _≅_ ]⁺ C} →
              (_ ∼⁺⟨ f⁺ ⟩  g⁺) ≃⁺ h⁺ → g⁺ ≃⁺ (_ ∼⁺⟨ reverse f⁺ ⟩ h⁺)
  ≅-shift {f⁺ = f⁺} {g⁺ = g⁺} {h⁺ = h⁺} eq = begin
    ∘ᵢ-tc g⁺                                      ≈⟨ introʳ (I.isoʳ f⁺) ⟩
    ∘ᵢ-tc g⁺ ∘ᵢ (∘ᵢ-tc f⁺ ∘ᵢ ∘ᵢ-tc (reverse f⁺))  ≈⟨ pullˡ eq ⟩
    ∘ᵢ-tc h⁺ ∘ᵢ ∘ᵢ-tc (reverse f⁺)                ∎
    where
      open HomReasoningᵢ
      open MR Core
      module I {A B} (f⁺ : A [ _≅_ ]⁺ B) = Morphism.Iso (IsGroupoid.iso TransitiveClosure-groupoid {f = f⁺})

  lift : ∀ {f⁺ : A [ _⇒_ ]⁺ B} → IsoPlus f⁺ → A [ _≅_ ]⁺ B
  lift [ iso ]            = [ record
    { from = _
    ; to   = _
    ; iso  = iso
    } ]
  lift (_ ∼⁺⟨ iso ⟩ iso′) = _ ∼⁺⟨ lift iso ⟩ lift iso′

  reduce-lift : ∀ {f⁺ : A [ _⇒_ ]⁺ B} (f′ : IsoPlus f⁺) → from (∘ᵢ-tc (lift f′)) ≡ ∘-tc f⁺
  reduce-lift [ f ]           = ≡.refl
  reduce-lift (_ ∼⁺⟨ f′ ⟩ f″) = ≡.cong₂ _∘_ (reduce-lift f″) (reduce-lift f′)

  lift-cong : ∀ {f⁺ g⁺ : A [ _⇒_ ]⁺ B} (f′ : IsoPlus f⁺) (g′ : IsoPlus g⁺) →
              f⁺ ≈⁺ g⁺ → lift f′ ≃⁺ lift g′
  lift-cong {_} {_} {f⁺} {g⁺} f′ g′ eq = ⌞ from-≈′ ⌟
    where
      open HomReasoning

      from-≈′ : from (∘ᵢ-tc (lift f′)) ≈ from (∘ᵢ-tc (lift g′))
      from-≈′ = begin
        from (∘ᵢ-tc (lift f′))  ≡⟨ reduce-lift f′ ⟩
        ∘-tc f⁺                 ≈⟨ eq ⟩
        ∘-tc g⁺                 ≡˘⟨ reduce-lift g′ ⟩
        from (∘ᵢ-tc (lift g′))  ∎

  lift-triangle : {f : A ⇒ B} {g : C ⇒ A} {h : C ⇒ B} {k : B ⇒ C} {i : B ⇒ A} {j : A ⇒ C} →
    f ∘ g ≈ h → (f′ : Iso f i) → (g′ : Iso g j) → (h′ : Iso h k) →
    lift (_ ∼⁺⟨ [ g′ ] ⟩ [ f′ ]) ≃⁺ lift [ h′ ]
  lift-triangle eq f′ g′ h′ = lift-cong (_ ∼⁺⟨ [ g′ ] ⟩ [ f′ ]) [ h′ ] eq

  lift-square : {f : A ⇒ B} {g : C ⇒ A} {h : D ⇒ B} {i : C ⇒ D} {j : D ⇒ C} {a : B ⇒ A} {b : A ⇒ C} {c : B ⇒ D} →
    f ∘ g ≈ h ∘ i → (f′ : Iso f a) → (g′ : Iso g b) → (h′ : Iso h c) → (i′ : Iso i j) →
    lift (_ ∼⁺⟨ [ g′ ] ⟩ [ f′ ]) ≃⁺ lift (_ ∼⁺⟨ [ i′ ] ⟩ [ h′ ])
  lift-square eq f′ g′ h′ i′ = lift-cong (_ ∼⁺⟨ [ g′ ] ⟩ [ f′ ]) (_ ∼⁺⟨ [ i′ ] ⟩ [ h′ ]) eq

  lift-pentagon : {f : A ⇒ B} {g : C ⇒ A} {h : D ⇒ C} {i : E ⇒ B} {j : D ⇒ E} {l : E ⇒ D}
                  {a : B ⇒ A} {b : A ⇒ C} {c : C ⇒ D} {d : B ⇒ E} →
    f ∘ g ∘ h ≈ i ∘ j →
    (f′ : Iso f a) → (g′ : Iso g b) → (h′ : Iso h c) → (i′ : Iso i d) → (j′ : Iso j l) →
    lift (_ ∼⁺⟨ _ ∼⁺⟨ [ h′ ] ⟩ [ g′ ] ⟩ [ f′ ]) ≃⁺ lift (_ ∼⁺⟨ [ j′ ] ⟩ [ i′ ])
  lift-pentagon eq f′ g′ h′ i′ j′ = lift-cong (_ ∼⁺⟨ _ ∼⁺⟨ [ h′ ] ⟩ [ g′ ] ⟩ [ f′ ]) (_ ∼⁺⟨ [ j′ ] ⟩ [ i′ ]) eq

module _ where
  open _≅_

  -- projecting isomorphism commutations to morphism commutations

  project-triangle : {g : A ≅ B} {f : C ≅ A} {h : C ≅ B} → g ∘ᵢ f ≈ᵢ h → from g ∘ from f ≈ from h
  project-triangle = from-≈

  project-square : {g : A ≅ B} {f : C ≅ A} {i : D ≅ B} {h : C ≅ D} → g ∘ᵢ f ≈ᵢ i ∘ᵢ h → from g ∘ from f ≈ from i ∘ from h
  project-square = from-≈

  -- direct lifting from morphism commutations to isomorphism commutations

  lift-triangle′ : {f : A ≅ B} {g : C ≅ A} {h : C ≅ B} → from f ∘ from g ≈ from h → f ∘ᵢ g ≈ᵢ h
  lift-triangle′ = ⌞_⌟

  lift-square′ : {f : A ≅ B} {g : C ≅ A} {h : D ≅ B} {i : C ≅ D} → from f ∘ from g ≈ from h ∘ from i → f ∘ᵢ g ≈ᵢ h ∘ᵢ i
  lift-square′ = ⌞_⌟

  lift-pentagon′ : {f : A ≅ B} {g : C ≅ A} {h : D ≅ C} {i : E ≅ B} {j : D ≅ E} →
                   from f ∘ from g ∘ from h ≈ from i ∘ from j → f ∘ᵢ g ∘ᵢ h ≈ᵢ i ∘ᵢ j
  lift-pentagon′ = ⌞_⌟

  open MR Core
  open HomReasoningᵢ
  open MR.GroupoidR _ Core-isGroupoid

  squares×≃⇒≃ : {f f′ : A ≅ B} {g : A ≅ C} {h : B ≅ D} {i i′ : C ≅ D} →
                CommutativeIso f g h i → CommutativeIso f′ g h i′ → i ≈ᵢ i′ → f ≈ᵢ f′
  squares×≃⇒≃ sq₁ sq₂ eq = MCore.isos×≈⇒≈ eq helper₁ (MCore.≅.sym helper₂) sq₁ sq₂
    where
      helper₁ = record { iso = ⁻¹-iso }
      helper₂ = record { iso = ⁻¹-iso }

  -- imagine a triangle prism, if all the sides and the top face commute, the bottom face commute.
  triangle-prism : {i′ : A ≅ B} {f′ : C ≅ A} {h′ : C ≅ B} {i : D ≅ E} {j : D ≅ A}
    {k : E ≅ B} {f : F ≅ D} {g : F ≅ C} {h : F ≅ E} →
    i′ ∘ᵢ f′ ≈ᵢ h′ →
    CommutativeIso i j k i′ → CommutativeIso f g j f′ → CommutativeIso h g k h′ →
    i ∘ᵢ f ≈ᵢ h
  triangle-prism {i′ = i′} {f′} {_} {i} {_} {k} {f} {g} {_} eq sq₁ sq₂ sq₃ =
    squares×≃⇒≃ glued sq₃ eq
    where
      glued : CommutativeIso (i ∘ᵢ f) g k (i′ ∘ᵢ f′)
      glued = ⟺ (glue (⟺ sq₁) (⟺ sq₂))

  elim-triangleˡ : {f : A ≅ B} {g : C ≅ A} {h : D ≅ C} {i : D ≅ B} {j : D ≅ A} →
                   f ∘ᵢ g ∘ᵢ h ≈ᵢ i → f ∘ᵢ j ≈ᵢ i → g ∘ᵢ h ≈ᵢ j
  elim-triangleˡ perim tri = MCore.mono _ _ (perim ○ ⟺ tri)

  elim-triangleˡ′ : {f : A ≅ B} {g : C ≅ A} {h : D ≅ C} {i : D ≅ B} {j : C ≅ B} →
                    f ∘ᵢ g ∘ᵢ h ≈ᵢ i → j ∘ᵢ h ≈ᵢ i → f ∘ᵢ g ≈ᵢ j
  elim-triangleˡ′ {f = f} {g} {h} {i} {j} perim tri = MCore.epi _ _ ( begin
    (f ∘ᵢ g) ∘ᵢ h ≈⟨ ⌞ assoc ⌟ ⟩
    f ∘ᵢ g ∘ᵢ h   ≈⟨ perim ⟩
    i             ≈˘⟨ tri ⟩
    j ∘ᵢ h        ∎ )

  cut-squareʳ : {g : A ≅ B} {f : A ≅ C} {h : B ≅ D} {i : C ≅ D} {j : B ≅ C} →
                CommutativeIso g f h i → i ∘ᵢ j ≈ᵢ h → j ∘ᵢ g ≈ᵢ f
  cut-squareʳ {g = g} {f = f} {h = h} {i = i} {j = j} sq tri = begin
    j ∘ᵢ g            ≈⟨ switch-fromtoˡ′ {f = i} {h = j} {k = h} tri ⟩∘⟨refl ⟩
    (i ⁻¹ ∘ᵢ h) ∘ᵢ g  ≈⟨ ⌞ assoc ⌟ ⟩
    i ⁻¹ ∘ᵢ h ∘ᵢ g    ≈˘⟨ switch-fromtoˡ′ {f = i} {h = f} {k = h ∘ᵢ g} (⟺ sq) ⟩
    f                 ∎
