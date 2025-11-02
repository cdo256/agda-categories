{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category

module Categories.Object.Subobject {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Data.Product
open import Data.Unit

open import Relation.Binary using (Poset)

open import Categories.Functor
open import Categories.Category.Slice
open import Categories.Category.SubCategory
open import Categories.Category.Construction.Thin
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Categories.Morphism.Notation

private
  module 𝒞 = Category 𝒞

-- The Full Subcategory of the over category 𝒞/c on monomorphisms
slice-mono : 𝒞.Obj → Category _ _ _
slice-mono c = FullSubCategory (Slice 𝒞 c) {I = Σ[ α ∈ 𝒞.Obj ](α ↣ c)} λ (_ , i) → sliceobj (mor i)
  where open Mor 𝒞
        open _↣_

-- Poset of subobjects for some c ∈ 𝒞
Subobjects : 𝒞.Obj → Poset _ _ _
Subobjects c = record
  { Carrier = 𝒞ᶜ.Obj
  ; _≈_ = 𝒞ᶜ [_≅_]
  ; _≤_ = 𝒞ᶜ [_,_]
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Mor.≅-isEquivalence 𝒞ᶜ
      ; reflexive = λ iso → Mor._≅_.from iso
      ; trans = λ {(α , f) (β , g) (γ , h)} i j → slicearr (chase f g h i j)
      }
    ; antisym = λ {(α , f) (β , g)} h i → record
      { from = h
      ; to = i
      ; iso = record
        { isoˡ = mono f _ _ (chase f g f h i ○ ⟺ 𝒞.identityʳ)
        ; isoʳ = mono g _ _ (chase g f g i h ○ ⟺ 𝒞.identityʳ)
        }
      }
    }
  }
  where
    𝒞ᶜ : Category _ _ _
    𝒞ᶜ = slice-mono c

    module 𝒞ᶜ = Category 𝒞ᶜ

    open Mor 𝒞 using (_↣_)
    open MR 𝒞
    open 𝒞.HomReasoning
    open _↣_

    chase : ∀ {α β γ : 𝒞.Obj} (f : 𝒞 [ α ↣ c ]) (g : 𝒞 [ β ↣ c ]) (h : 𝒞 [ γ ↣ c ])
            → (i : 𝒞ᶜ [ (α , f) , (β , g) ]) → (j : 𝒞ᶜ [ (β , g) , (γ , h) ])
            → 𝒞 [ 𝒞 [ mor h ∘ 𝒞 [ Slice⇒.h j ∘ Slice⇒.h i ] ] ≈ mor f ]
    chase f g h i j = begin
      𝒞 [ mor h ∘ 𝒞 [ Slice⇒.h j ∘ Slice⇒.h i ] ] ≈⟨ pullˡ (Slice⇒.△ j)  ⟩
      𝒞 [ mor g ∘ Slice⇒.h i ]                    ≈⟨ Slice⇒.△ i ⟩
      mor f ∎
