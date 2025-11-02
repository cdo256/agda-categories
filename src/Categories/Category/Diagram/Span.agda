{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category

-- Some basic facts about Spans in some category 𝒞.
--
-- For the Category instances for these, you can look at the following modules
--    Categories.Category.Construction.Spans
--    Categories.Bicategory.Construction.Spans
module Categories.Category.Diagram.Span {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (_$_)

open import Categories.Diagram.Pullback 𝒞
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning
open Equiv

open Pullback

private
  variable
    A B C D E : Obj

--------------------------------------------------------------------------------
-- Spans, and Span morphisms

infixr 9 _∘ₛ_

record Span (X Y : Obj) : Set (o ⊔ ℓ) where
  field
    M : Obj
    dom : M ⇒ X
    cod : M ⇒ Y

open Span

id-span : Span A A
id-span {A} = record
  { M = A
  ; dom = id
  ; cod = id
  }

record Span⇒ {X Y} (f g : Span X Y) : Set (o ⊔ ℓ ⊔ e) where
  field
    arr : M f ⇒ M g
    commute-dom : dom g ∘ arr ≈ dom f
    commute-cod : cod g ∘ arr ≈ cod f

open Span⇒

id-span⇒ : ∀ {f : Span A B} → Span⇒ f f
id-span⇒ = record
  { arr = id
  ; commute-dom = identityʳ
  ; commute-cod = identityʳ
  }

_∘ₛ_ : ∀ {f g h : Span A B} → (α : Span⇒ g h) → (β : Span⇒ f g) → Span⇒ f h
_∘ₛ_ {f = f} {g = g} {h = h} α β = record
  { arr = arr α ∘ arr β
  ; commute-dom = begin
    dom h ∘ arr α ∘ arr β ≈⟨ pullˡ (commute-dom α) ⟩
    dom g ∘ arr β ≈⟨ commute-dom β ⟩
    dom f ∎
  ; commute-cod = begin
    cod h ∘ arr α ∘ arr β ≈⟨ pullˡ (commute-cod α) ⟩
    cod g ∘ arr β ≈⟨ commute-cod β ⟩
    cod f ∎
  }

--------------------------------------------------------------------------------
-- Span Compositions

module Compositions (_×ₚ_ : ∀ {X Y Z} (f : X ⇒ Z) → (g : Y ⇒ Z) → Pullback f g) where

  _⊚₀_ : Span B C → Span A B → Span A C
  f ⊚₀ g =
    let g×ₚf = (cod g) ×ₚ (dom f)
    in record
        { M = P g×ₚf
        ; dom = dom g ∘ p₁ g×ₚf
        ; cod = cod f ∘ p₂ g×ₚf
        }

  _⊚₁_ : {f f′ : Span B C} {g g′ : Span A B} → Span⇒ f f′ → Span⇒ g g′ → Span⇒ (f ⊚₀ g) (f′ ⊚₀ g′)
  _⊚₁_  {f = f} {f′ = f′} {g = g} {g′ = g′} α β =
    let pullback = (cod g) ×ₚ (dom f)
        pullback′ = (cod g′) ×ₚ (dom f′)
    in record
      { arr = universal pullback′ {h₁ = arr β ∘ p₁ pullback} {h₂ = arr α ∘ p₂ pullback} $ begin
          cod g′ ∘ arr β ∘ p₁ pullback ≈⟨ pullˡ (commute-cod β) ⟩
          cod g ∘ p₁ pullback          ≈⟨ commute pullback ⟩
          dom f ∘ p₂ pullback          ≈⟨ pushˡ (⟺ (commute-dom α)) ⟩
          dom f′ ∘ arr α ∘ p₂ pullback ∎
      ; commute-dom = begin
          (dom g′ ∘ p₁ pullback′) ∘ universal pullback′ _ ≈⟨ pullʳ (p₁∘universal≈h₁ pullback′) ⟩
          dom g′ ∘ arr β ∘ p₁ pullback                    ≈⟨ pullˡ (commute-dom β) ⟩
          dom g ∘ p₁ pullback                             ∎
      ; commute-cod = begin
          (cod f′ ∘ p₂ pullback′) ∘ universal pullback′ _ ≈⟨ pullʳ (p₂∘universal≈h₂ pullback′) ⟩
          cod f′ ∘ arr α ∘ p₂ pullback                    ≈⟨ pullˡ (commute-cod α) ⟩
          cod f ∘ p₂ pullback                             ∎
      }
