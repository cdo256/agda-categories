{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module Categories.Category.Construction.SetoidIndexedFamily {o ℓ e} (C : Category o ℓ e) where

open import Level using (Level; _⊔_; suc)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Composition as Comp
import Function.Construct.Identity as Id
open import Relation.Binary using (Setoid; Reflexive; Symmetric; Transitive)

private
  module C = Category C

open import Categories.Morphism C using (_≅_)
open C.HomReasoning

record Family (ℓI ℓI' : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ ℓI ⊔ ℓI')) where
  constructor fam
  field
    I : Setoid ℓI ℓI'

  open Setoid I public renaming (Carrier to I₀)

  field
    X : I₀ → C.Obj
    resp : ∀ {i j : I₀} → i ≈ j → X i ≅ X j

  module resp {i j : I₀} (p : i ≈ j) = _≅_ (resp p)

  field
    resp-refl : ∀ {i : I₀} → resp.from (refl {i}) C.≈ C.id
    resp-sym : ∀ {i j : I₀} (p : i ≈ j) → resp.from (sym p) C.≈ resp.to p
    resp-trans : ∀ {i j k : I₀} (p : i ≈ j) (q : j ≈ k)
      → resp.from (trans p q) C.≈ resp.from q C.∘ resp.from p
    resp-irr : ∀ {i j : I₀} (p q : i ≈ j) → resp.from p C.≈ resp.from q

record Hom {ℓI ℓI'} (A : Family ℓI ℓI') (B : Family ℓI ℓI')
  : Set (o ⊔ ℓ ⊔ e ⊔ ℓI ⊔ ℓI') where
  constructor hom
  private
    module A = Family A
    module B = Family B

  field
    u : Func A.I B.I

  module u = Func u
  field
    f : (i : A.I₀) → A.X i C.⇒ B.X (u ⟨$⟩ i)
    coh : {i j : A.I₀} → (p : i A.≈ j)
        →   B.resp.from (u.cong p) C.∘ f i
        C.≈ f j C.∘ A.resp.from p

record _≈_ {ℓI ℓI'} {A : Family ℓI ℓI'} {B : Family ℓI ℓI'}
  (F G : Hom A B) : Set (o ⊔ ℓ ⊔ e ⊔ ℓI ⊔ ℓI') where
  constructor hom-≈
  private
    module A = Family A
    module B = Family B
    module F = Hom F
    module G = Hom G

  field
    u≈ : {i : A.I₀} → F.u ⟨$⟩ i B.≈ G.u ⟨$⟩ i
    f≈ : {i : A.I₀} → B.resp.from u≈ C.∘ F.f i C.≈ G.f i

open Hom
open _≈_

id : ∀ {ℓI ℓI'} {A : Family ℓI ℓI'} → Hom A A
id = record
  { u = Id.function _
  ; f = λ _ → C.id
  ; coh = λ _ → C.Equiv.trans C.identityʳ (C.Equiv.sym C.identityˡ)
  }

infixr 9 _∘_
_∘_ : ∀ {ℓI ℓI'} {A : Family ℓI ℓI'} {B : Family ℓI ℓI'} {D : Family ℓI ℓI'}
  → Hom B D → Hom A B → Hom A D
_∘_ {A = A} {B = B} {D = D} g f = record
  { u = gf
  ; f = λ i → g.f (f.u ⟨$⟩ i) C.∘ f.f i
  ; coh = comp-coh
  }
  where
  module A = Family A
  module B = Family B
  module D = Family D
  module f = Hom f
  module g = Hom g

  gf : Func A.I D.I
  gf = Comp.function f.u g.u

  module gf = Func gf

  comp-coh : {i j : A.I₀} → (p : i A.≈ j)
    → D.resp.from (gf.cong p) C.∘ (g.f (f.u ⟨$⟩ i) C.∘ f.f i)
    C.≈ (g.f (f.u ⟨$⟩ j) C.∘ f.f j) C.∘ A.resp.from p
  comp-coh {i} {j} p = begin
    D.resp.from (gf.cong p) C.∘ (g.f (f.u ⟨$⟩ i) C.∘ f.f i)
      ≈⟨ C.sym-assoc ⟩
    (D.resp.from (g.u.cong (f.u.cong p)) C.∘ g.f (f.u ⟨$⟩ i)) C.∘ f.f i
      ≈⟨ g.coh (f.u.cong p) ⟩∘⟨refl ⟩
    (g.f (f.u ⟨$⟩ j) C.∘ B.resp.from (f.u.cong p)) C.∘ f.f i
      ≈⟨ C.assoc ⟩
    g.f (f.u ⟨$⟩ j) C.∘ (B.resp.from (f.u.cong p) C.∘ f.f i)
      ≈⟨ refl⟩∘⟨ f.coh p ⟩
    g.f (f.u ⟨$⟩ j) C.∘ (f.f j C.∘ A.resp.from p)
      ≈⟨ C.sym-assoc ⟩
    (g.f (f.u ⟨$⟩ j) C.∘ f.f j) C.∘ A.resp.from p
      ∎

≈-refl : ∀ {ℓI ℓI'} {A B : Family ℓI ℓI'}
  → Reflexive (_≈_ {A = A} {B = B})
≈-refl {B = B} = record
  { u≈ = B.refl
  ; f≈ = C.Equiv.trans (C.∘-resp-≈ˡ B.resp-refl) C.identityˡ
  }
  where module B = Family B

≈-sym : ∀ {ℓI ℓI'} {A B : Family ℓI ℓI'}
  → Symmetric (_≈_ {A = A} {B = B})
≈-sym {B = B} {F} {G} α = record
  { u≈ = B.sym α.u≈
  ; f≈ = λ {i} → begin
      B.resp.from (B.sym α.u≈) C.∘ G.f i
        ≈⟨ C.∘-resp-≈ˡ (B.resp-sym α.u≈) ⟩
      B.resp.to α.u≈ C.∘ G.f i
        ≈⟨ C.∘-resp-≈ʳ (C.Equiv.sym α.f≈) ⟩
      B.resp.to α.u≈ C.∘ (B.resp.from α.u≈ C.∘ F.f i)
        ≈⟨ C.sym-assoc ⟩
      (B.resp.to α.u≈ C.∘ B.resp.from α.u≈) C.∘ F.f i
        ≈⟨ B.resp.isoˡ α.u≈ ⟩∘⟨refl ⟩
      C.id C.∘ F.f i
        ≈⟨ C.identityˡ ⟩
      F.f i
        ∎
  }
  where
  module B = Family B
  module F = Hom F
  module G = Hom G
  module α = _≈_ α

≈-trans : ∀ {ℓI ℓI'} {A : Family ℓI ℓI'} {B : Family ℓI ℓI'}
  → Transitive (_≈_ {A = A} {B = B})
≈-trans {B = B} {F} {G} {H} α β = record
  { u≈ = B.trans α.u≈ β.u≈
  ; f≈ = λ {i} → begin
      B.resp.from (B.trans α.u≈ β.u≈) C.∘ F.f i
        ≈⟨ C.∘-resp-≈ˡ (B.resp-trans α.u≈ β.u≈) ⟩
      (B.resp.from β.u≈ C.∘ B.resp.from α.u≈) C.∘ F.f i
        ≈⟨ C.assoc ⟩
      B.resp.from β.u≈ C.∘ (B.resp.from α.u≈ C.∘ F.f i)
        ≈⟨ refl⟩∘⟨ α.f≈ ⟩
      B.resp.from β.u≈ C.∘ G.f i
        ≈⟨ β.f≈ ⟩
      H.f i
        ∎
  }
  where
  module B = Family B
  module F = Hom F
  module G = Hom G
  module H = Hom H
  module α = _≈_ α
  module β = _≈_ β

∘-resp-≈ : ∀ {ℓI ℓI'}
  {A B D : Family ℓI ℓI'}
  {f h : Hom B D} {g i : Hom A B}
  → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {A = A} {B = B} {D = D} {f} {h} {g} {i} α β = record
  { u≈ = D.trans (f.u.cong β.u≈) α.u≈
  ; f≈ = λ {x} → begin
      D.resp.from (D.trans (f.u.cong β.u≈) α.u≈) C.∘ (f.f (g.u ⟨$⟩ x) C.∘ g.f x)
        ≈⟨ C.∘-resp-≈ˡ (D.resp-trans (f.u.cong β.u≈) α.u≈) ⟩
      (D.resp.from α.u≈ C.∘ D.resp.from (f.u.cong β.u≈)) C.∘ (f.f (g.u ⟨$⟩ x) C.∘ g.f x)
        ≈⟨ C.assoc ⟩
      D.resp.from α.u≈ C.∘ (D.resp.from (f.u.cong β.u≈) C.∘ (f.f (g.u ⟨$⟩ x) C.∘ g.f x))
        ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
      D.resp.from α.u≈ C.∘ ((D.resp.from (f.u.cong β.u≈) C.∘ f.f (g.u ⟨$⟩ x)) C.∘ g.f x)
        ≈⟨ C.sym-assoc ⟩
      (D.resp.from α.u≈ C.∘ (D.resp.from (f.u.cong β.u≈) C.∘ f.f (g.u ⟨$⟩ x))) C.∘ g.f x
        ≈⟨ (refl⟩∘⟨ f.coh β.u≈) ⟩∘⟨refl ⟩
      (D.resp.from α.u≈ C.∘ (f.f (i.u ⟨$⟩ x) C.∘ B.resp.from β.u≈)) C.∘ g.f x
        ≈⟨ C.sym-assoc ⟩∘⟨refl ⟩
      ((D.resp.from α.u≈ C.∘ f.f (i.u ⟨$⟩ x)) C.∘ B.resp.from β.u≈) C.∘ g.f x
        ≈⟨ C.assoc ⟩
      (D.resp.from α.u≈ C.∘ f.f (i.u ⟨$⟩ x)) C.∘ (B.resp.from β.u≈ C.∘ g.f x)
        ≈⟨ α.f≈ ⟩∘⟨ β.f≈ ⟩
      h.f (i.u ⟨$⟩ x) C.∘ i.f x
        ∎
  }
  where
  module A = Family A
  module B = Family B
  module D = Family D
  module f = Hom f
  module h = Hom h
  module g = Hom g
  module i = Hom i
  module α = _≈_ α
  module β = _≈_ β

CategoryOfFamilies : ∀ ℓI ℓI'
  → Category (suc (o ⊔ ℓ ⊔ e ⊔ ℓI ⊔ ℓI'))
              (o ⊔ ℓ ⊔ e ⊔ ℓI ⊔ ℓI')
              (o ⊔ ℓ ⊔ e ⊔ ℓI ⊔ ℓI')
CategoryOfFamilies ℓI ℓI' = record
  { Obj = Family ℓI ℓI'
  ; _⇒_ = Hom
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = λ {A B C D f g h} → assoc {A} {B} {C} {D} {f} {g} {h}
  ; sym-assoc = λ {A B C D f g h} → sym-assoc {A} {B} {C} {D} {f} {g} {h}
  ; identityˡ = λ {A B f} → identityˡ {A} {B} {f}
  ; identityʳ = λ {A B f} → identityʳ {A} {B} {f}
  ; identity² = λ {A} → identity² {A}
  ; equiv = λ {A} {B} → record
    { refl = ≈-refl {A = A} {B = B}
    ; sym = ≈-sym {A = A} {B = B}
    ; trans = ≈-trans {A = A} {B = B}
    }
  ; ∘-resp-≈ = λ {A} {B} {D} {f} {h} {g} {i} → ∘-resp-≈ {A = A} {B = B} {D = D} {f} {h} {g} {i}
  }
  where
  assoc : ∀ {A B C₁ D} {f : Hom A B} {g : Hom B C₁} {h : Hom C₁ D}
    → ((h ∘ g) ∘ f) ≈ (h ∘ (g ∘ f))
  assoc {D = D} {f} {g} {h}
    = record
    { u≈ = D.refl
    ; f≈ = λ {i} → begin
        D.resp.from D.refl C.∘ ((h.f (g.u ⟨$⟩ (f.u ⟨$⟩ i)) C.∘ g.f (f.u ⟨$⟩ i)) C.∘ f.f i)
          ≈⟨ C.∘-resp-≈ˡ D.resp-refl ⟩
        C.id C.∘ ((h.f (g.u ⟨$⟩ (f.u ⟨$⟩ i)) C.∘ g.f (f.u ⟨$⟩ i)) C.∘ f.f i)
          ≈⟨ C.identityˡ ⟩
        (h.f (g.u ⟨$⟩ (f.u ⟨$⟩ i)) C.∘ g.f (f.u ⟨$⟩ i)) C.∘ f.f i
          ≈⟨ C.assoc ⟩
        h.f (g.u ⟨$⟩ (f.u ⟨$⟩ i)) C.∘ (g.f (f.u ⟨$⟩ i) C.∘ f.f i)
          ∎
    }
    where
    module D = Family D
    module f = Hom f
    module g = Hom g
    module h = Hom h

  sym-assoc : ∀ {A B C₁ D} {f : Hom A B} {g : Hom B C₁} {h : Hom C₁ D}
    → (h ∘ (g ∘ f)) ≈ ((h ∘ g) ∘ f)
  sym-assoc {D = D} {f} {g} {h}
    = record
    { u≈ = D.refl
    ; f≈ = λ {i} → begin
        D.resp.from D.refl C.∘ (h.f (g.u ⟨$⟩ (f.u ⟨$⟩ i)) C.∘ (g.f (f.u ⟨$⟩ i) C.∘ f.f i))
          ≈⟨ C.∘-resp-≈ˡ D.resp-refl ⟩
        C.id C.∘ (h.f (g.u ⟨$⟩ (f.u ⟨$⟩ i)) C.∘ (g.f (f.u ⟨$⟩ i) C.∘ f.f i))
          ≈⟨ C.identityˡ ⟩
        h.f (g.u ⟨$⟩ (f.u ⟨$⟩ i)) C.∘ (g.f (f.u ⟨$⟩ i) C.∘ f.f i)
          ≈⟨ C.sym-assoc ⟩
        (h.f (g.u ⟨$⟩ (f.u ⟨$⟩ i)) C.∘ g.f (f.u ⟨$⟩ i)) C.∘ f.f i
          ∎
    }
    where
    module D = Family D
    module f = Hom f
    module g = Hom g
    module h = Hom h

  identityˡ : ∀ {A B} {f : Hom A B} → (id ∘ f) ≈ f
  identityˡ {B = B} {f} = record
    { u≈ = B.refl
    ; f≈ = λ {i} → begin
        B.resp.from B.refl C.∘ (C.id C.∘ f.f i)
          ≈⟨ C.∘-resp-≈ˡ B.resp-refl ⟩
        C.id C.∘ (C.id C.∘ f.f i)
          ≈⟨ C.identityˡ ⟩
        C.id C.∘ f.f i
          ≈⟨ C.identityˡ ⟩
        f.f i
          ∎
    }
    where
    module B = Family B
    module f = Hom f

  identityʳ : ∀ {A B} {f : Hom A B} → (f ∘ id) ≈ f
  identityʳ {B = B} {f} = record
    { u≈ = B.refl
    ; f≈ = λ {i} → begin
        B.resp.from B.refl C.∘ (f.f i C.∘ C.id)
          ≈⟨ C.∘-resp-≈ˡ B.resp-refl ⟩
        C.id C.∘ (f.f i C.∘ C.id)
          ≈⟨ C.identityˡ ⟩
        f.f i C.∘ C.id
          ≈⟨ C.identityʳ ⟩
        f.f i
          ∎
    }
    where
    module B = Family B
    module f = Hom f

  identity² : ∀ {A} → (id {A = A} ∘ id) ≈ id
  identity² {A} = record
    { u≈ = A.refl
    ; f≈ = λ {i} → begin
        A.resp.from A.refl C.∘ (C.id C.∘ C.id)
          ≈⟨ C.∘-resp-≈ˡ A.resp-refl ⟩
        C.id C.∘ (C.id C.∘ C.id)
          ≈⟨ C.identityˡ ⟩
        C.id C.∘ C.id
          ≈⟨ C.identity² ⟩
        C.id
          ∎
    }
    where module A = Family A
