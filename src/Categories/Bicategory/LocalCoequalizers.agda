{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Bicategory

module Categories.Bicategory.LocalCoequalizers {o ℓ e t} (𝒞 : Bicategory o ℓ e t)  where

open import Categories.Diagram.Coequalizer using (Coequalizer; Coequalizers)
open import Level using (_⊔_)
open import Categories.Functor.Properties using (PreservesCoequalizers)
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞


record LocalCoequalizers : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  field
    localCoequalizers : (A B : Obj) → Coequalizers (hom A B)
    precompPreservesCoequalizer : {A B E : Obj} → (f : E ⇒₁ A)
      → PreservesCoequalizers (-⊚_ {E} {A} {B} f)
    postcompPreservesCoequalizer : {A B E : Obj} → (f : B ⇒₁ E)
      → PreservesCoequalizers (_⊚- {B} {E} {A} f)

open LocalCoequalizers

module _ (localcoeq : LocalCoequalizers)
         {A B E : Obj} {X Y : A ⇒₁ B} {α β : X ⇒₂ Y} where

  _coeq-◁_ : (coeq : Coequalizer (hom A B) α β) (f : E ⇒₁ A)
           → Coequalizer (hom E B) (α ◁ f) (β ◁ f)
  coeq coeq-◁ f = record
    { obj = obj ∘₁ f
    ; arr = arr ◁ f
    ; isCoequalizer = precompPreservesCoequalizer localcoeq f {coeq = coeq}
    }
    where
      open Coequalizer coeq

  _▷-coeq_ : (f : B ⇒₁ E) (coeq : Coequalizer (hom A B) α β)
                      → Coequalizer (hom A E) (f ▷ α) (f ▷ β)
  f ▷-coeq coeq = record
    { obj = f ∘₁ obj
    ; arr = f ▷ arr
    ; isCoequalizer = postcompPreservesCoequalizer localcoeq f {coeq = coeq}
    }
    where
      open Coequalizer coeq
