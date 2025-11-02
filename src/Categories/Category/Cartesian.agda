{-# OPTIONS --cubical-compatible --without-K --safe #-}

open import Categories.Category using (Category)

-- Defines the following properties of a Category:
-- Cartesian -- a Cartesian category is a category with all products

--  (for the induced Monoidal structure, see Cartesian.Monoidal)

module Categories.Category.Cartesian {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (levelOfTerm)
open import Data.Nat using (ℕ; zero; suc)

open Category 𝒞
open HomReasoning

open import Categories.Category.BinaryProducts 𝒞 using (BinaryProducts; module BinaryProducts)
open import Categories.Object.Terminal 𝒞 using (Terminal)

private
  variable
    A B C D W X Y Z : Obj
    f f′ g g′ h i : A ⇒ B

-- Cartesian monoidal category
record Cartesian : Set (levelOfTerm 𝒞) where
  field
    terminal : Terminal
    products : BinaryProducts
  open BinaryProducts products using (_×_)

  power : Obj → ℕ → Obj
  power A 0 = Terminal.⊤ terminal
  power A 1 = A
  power A (suc (suc n)) = A × power A (suc n)
