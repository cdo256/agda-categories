{-# OPTIONS --cubical-compatible --without-K --safe #-}
module Categories.Category.Restriction.Construction.Kleisli where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Restriction using (Restriction)
open import Categories.Category.Monoidal.CounitalCopy.Restriction using (restriction)
open import Categories.Monad.EquationalLifting using (EquationalLiftingMonad)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Monoidal.Construction.Kleisli.CounitalCopy using (Kleisli-CounitalCopy)


private
  variable
    o ℓ e : Level

-- The Kleisli category of an equational lifting monad is a restriction category.

module _ {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) (ELM : EquationalLiftingMonad cartesian) where
  open EquationalLiftingMonad ELM using (M)

  Kleisli-Restriction : Restriction (Kleisli M)
  Kleisli-Restriction = restriction (Kleisli-CounitalCopy cartesian ELM)
