{-# OPTIONS --cubical-compatible --without-K --safe #-}

--------------------------------------------------------------------------------
-- A simple reflection based solver for categories.
--
-- Based off 'Tactic.MonoidSolver' from 'agda-stdlib'
--------------------------------------------------------------------------------

open import Categories.Category

module Categories.Tactic.Category where

open import Level
open import Function using (_⟨_⟩_)

open import Data.Bool    as Bool    using (Bool; _∨_; if_then_else_)
open import Data.Maybe   as Maybe   using (Maybe; just; nothing; maybe)
open import Data.List    as List    using (List; _∷_; [])
open import Data.Product as Product using (_×_; _,_)

open import Agda.Builtin.Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term using (getName; _⋯⟅∷⟆_)
open import Reflection.TCM.Syntax

module _ {o ℓ e} (𝒞 : Category o ℓ e) where

  open Category 𝒞
  open HomReasoning
  open Equiv

  private
    variable
      A B C : Obj
      f g   : A ⇒ B

  --------------------------------------------------------------------------------
  -- An 'Expr' reifies the parentheses/identity morphisms of some series of
  -- compositions of morphisms into a data structure. In fact, this is also
  -- a category!
  --------------------------------------------------------------------------------
  data Expr : Obj → Obj → Set (o ⊔ ℓ) where
    _∘′_ : ∀ {A B C} → Expr B C → Expr A B → Expr A C
    id′  : ∀ {A} → Expr A A
    [_↑] : ∀ {A B} → A ⇒ B → Expr A B

  -- Embed a morphism in 'Expr' back into '𝒞' without normalizing.
  [_↓] : Expr A B → A ⇒ B
  [ f ∘′ g ↓] = [ f ↓] ∘ [ g ↓]
  [ id′ ↓]    = id
  [ [ f ↑] ↓] = f

  -- Convert an 'Expr' back into a morphism, while normalizing
  --
  -- This actually embeds the morphism into the category of copresheaves
  -- on 𝒞, which obeys the category laws up to beta-eta equality.
  -- This lets us normalize away all the associations/identity morphisms.
  embed : Expr B C → A ⇒ B → A ⇒ C
  embed (f ∘′ g) h  = embed f (embed g h)
  embed id′ h       = h
  embed [ f ↑] h    = f ∘ h


  preserves-≈′ : ∀ (f : Expr B C) → (h : A ⇒ B) → embed f id ∘ h ≈ embed f h
  preserves-≈′ id′ f      = identityˡ
  preserves-≈′ [ x ↑] f   = ∘-resp-≈ˡ identityʳ
  preserves-≈′ (f ∘′ g) h = begin
    embed (f ∘′ g) id ∘ h         ≡⟨⟩
    embed f (embed g id) ∘ h      ≈˘⟨ preserves-≈′ f (embed g id) ⟩∘⟨refl ⟩
    (embed f id ∘ embed g id) ∘ h ≈⟨ assoc  ⟩
    embed f id ∘ embed g id ∘ h   ≈⟨ refl⟩∘⟨ preserves-≈′ g h ⟩
    embed f id ∘ embed g h        ≈⟨ preserves-≈′ f (embed g h) ⟩
    embed (f ∘′ g) h              ∎

  preserves-≈ : ∀ (f : Expr A B) → embed f id ≈ [ f ↓]
  preserves-≈ id′      = refl
  preserves-≈ [ x ↑]   = identityʳ
  preserves-≈ (f ∘′ g) = begin
    embed (f ∘′ g) id       ≈˘⟨ preserves-≈′ f (embed g id) ⟩
    embed f id ∘ embed g id ≈⟨ preserves-≈ f ⟩∘⟨ preserves-≈ g ⟩
    [ f ↓] ∘ [ g ↓]         ≡⟨⟩
    [ f ∘′ g ↓]             ∎

--------------------------------------------------------------------------------
-- Reflection Helpers
--------------------------------------------------------------------------------

_==_ = primQNameEquality
{-# INLINE _==_ #-}

getArgs : Term → Maybe (Term × Term)
getArgs (def _ xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (vArg x ∷ vArg y ∷ []) = just (x , y)
  go (x ∷ xs)               = go xs
  go _                      = nothing
getArgs _ = nothing

--------------------------------------------------------------------------------
-- Getting Category Names
--------------------------------------------------------------------------------

record CategoryNames : Set where
  field
    is-∘ : Name → Bool
    is-id : Name → Bool

buildMatcher : Name → Maybe Name → Name → Bool
buildMatcher n nothing  x = n == x
buildMatcher n (just m) x = n == x ∨ m == x

findCategoryNames : Term → TC CategoryNames
findCategoryNames cat = do
  ∘-altName ← normalise (def (quote Category._∘_) (3 ⋯⟅∷⟆ cat ⟨∷⟩ []))
  id-altName ← normalise (def (quote Category.id) (3 ⋯⟅∷⟆ cat ⟨∷⟩ []))
  returnTC record
    { is-∘ = buildMatcher (quote Category._∘_) (getName ∘-altName)
    ; is-id = buildMatcher (quote Category.id) (getName id-altName)
    }

--------------------------------------------------------------------------------
-- Constructing an Expr
--------------------------------------------------------------------------------

″id″ : Term
″id″ = quote id′ ⟨ con ⟩ []

″[_↑]″ : Term → Term
″[ t ↑]″ = quote [_↑] ⟨ con ⟩ (t ⟨∷⟩ [])

module _ (names : CategoryNames) where

  open CategoryNames names

  mutual
    ″∘″ : List (Arg Term) → Term
    ″∘″ (x ⟨∷⟩ y ⟨∷⟩ xs) = quote _∘′_ ⟨ con ⟩ buildExpr x ⟨∷⟩ buildExpr y ⟨∷⟩ []
    ″∘″ (x ∷ xs) = ″∘″ xs
    ″∘″ _ = unknown

    buildExpr : Term → Term
    buildExpr t@(def n xs) =
      if (is-∘ n)
        then ″∘″ xs
      else if (is-id n)
        then ″id″
      else
        ″[ t ↑]″
    buildExpr t@(con n xs) =
      if (is-∘ n)
        then ″∘″ xs
      else if (is-id n)
        then ″id″
      else
        ″[ t ↑]″
    buildExpr t = ″[ t ↑]″

--------------------------------------------------------------------------------
-- Constructing the Solution
--------------------------------------------------------------------------------

constructSoln : Term → CategoryNames → Term → Term → Term
constructSoln cat names lhs rhs =
  quote Category.Equiv.trans ⟨ def ⟩ 3 ⋯⟅∷⟆ cat ⟨∷⟩
    (quote Category.Equiv.sym ⟨ def ⟩ 3 ⋯⟅∷⟆ cat ⟨∷⟩
      (quote preserves-≈ ⟨ def ⟩ 3 ⋯⟅∷⟆ cat ⟨∷⟩ buildExpr names lhs ⟨∷⟩ []) ⟨∷⟩ [])
    ⟨∷⟩
    (quote preserves-≈ ⟨ def ⟩ 3 ⋯⟅∷⟆ cat ⟨∷⟩ buildExpr names rhs ⟨∷⟩ [])
    ⟨∷⟩ []

solve-macro : Term → Term → TC _
solve-macro mon hole = do
  hole′ ← inferType hole >>= normalise
  names ← findCategoryNames mon
  just (lhs , rhs) ← returnTC (getArgs hole′)
    where nothing → typeError (termErr hole′ ∷ [])
  let soln = constructSoln mon names lhs rhs
  unify hole soln

macro
  solve : Term → Term → TC _
  solve = solve-macro

