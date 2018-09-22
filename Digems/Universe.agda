module Digems.Universe where

open import Digems.Prelude
open import Digems.Universe.Opaque
  public

-- * Sum-of-product universe
-- ** Code

data Atom (n : ℕ) : Set where
  K : (κ : Konst) → Atom n 
  I : (ν : Fin n) → Atom n

Prod : ℕ → Set
Prod = List ∘ Atom

Sum : ℕ → Set
Sum = List ∘ Prod

-- ** Interpretation

Setⁿ : ℕ → Set₁
Setⁿ n = Fin n → Set

⟦_⟧A : {n : ℕ} → Atom n → Setⁿ n → Set
⟦ K κ ⟧A X = ⟦ κ ⟧K
⟦ I ν ⟧A X = X ν 

⟦_⟧P : {n : ℕ} → Prod n → Setⁿ n → Set
⟦ π ⟧P X = All (λ α → ⟦ α ⟧A X) π

⟦_⟧S : {n : ℕ} → Sum n → Setⁿ n → Set
⟦ σ ⟧S X = Any (λ π → ⟦ π ⟧P X) σ

-- ** Decidable equality

module DecEq {n : ℕ}(Rec : Setⁿ n)(_≟Rec_ : ∀{v}(x y : Rec v) → Dec (x ≡ y)) where

  _≟Atom_ : (α₁ α₂ : Atom n) → Dec (α₁ ≡ α₂)
  I i    ≟Atom I j with i ≟F j
  ...| yes refl = yes refl
  ...| no  ¬p   = no λ { refl → ¬p refl }   
  (K κ₁) ≟Atom (K κ₂) with κ₁ ≟Konst κ₂
  ...| yes refl = yes refl
  ...| no  ¬p  = no λ { refl → ¬p refl }
  I _ ≟Atom (K _) = no λ ()
  (K _) ≟Atom I _ = no λ ()

  _≟A_ :  ∀ {α} → (a₁ a₂ : ⟦ α ⟧A Rec) → Dec (a₁ ≡ a₂)
  _≟A_ {K κ} k₁ k₂ = k₁ ≟K k₂
  _≟A_ {I i} x  y  = x ≟Rec y

  _≟P_ : ∀ {π} → (p₁ p₂ : ⟦ π ⟧P Rec) → Dec (p₁ ≡ p₂)
  _≟P_ {[]} [] [] = yes refl
  _≟P_ {α ∷ π} (a₁ ∷ p₁) (a₂ ∷ p₂) with _≟A_ {α} a₁ a₂
  ... | no ¬p = no (λ { refl → ¬p refl })
  ... | yes refl with p₁ ≟P p₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }

  _≟S_ : ∀ {σ} → (s₁ s₂ : ⟦ σ ⟧S Rec) → Dec (s₁ ≡ s₂)
  _≟S_ {[]} () _
  _≟S_ {π ∷ σ} (here p₁) (here p₂) with p₁ ≟P p₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  _≟S_ {π ∷ σ} (here p₁) (there s₂) = no λ ()
  _≟S_ {π ∷ σ} (there s₁) (here s₂) = no λ ()
  _≟S_ {π ∷ σ} (there s₁) (there s₂) with s₁ ≟S s₂
  ... | yes refl = yes refl
  ... | no ¬p = no (λ { refl → ¬p refl })

-- ** Sum-of-product view

Constr : {n : ℕ} → Sum n → Set
Constr σ = Fin (length σ)

typeOf : {n : ℕ}(σ : Sum n) → Constr σ → Prod n
typeOf [] ()
typeOf (π ∷ σ) zero = π
typeOf (π ∷ σ) (suc C) = typeOf σ C

inj : {n : ℕ}{σ : Sum n}{X : Setⁿ n} → (C : Constr σ) → ⟦ typeOf σ C ⟧P X → ⟦ σ ⟧S X
inj {σ = []} () _
inj {σ = π ∷ σ} zero p = here p
inj {σ = x ∷ σ} (suc C) p = there (inj C p)

data SOP {n : ℕ}{σ : Sum n}{X : Setⁿ n} : ⟦ σ ⟧S X → Set where
  tag : (C : Constr σ)(p : ⟦ typeOf σ C ⟧P X) → SOP (inj C p)

sop : {n : ℕ}{σ : Sum n}{X : Setⁿ n} → (s : ⟦ σ ⟧S X) → SOP s
sop (here p) = tag zero p
sop (there s) with sop s
... | tag C p = tag (suc C) p

match : {n : ℕ}{σ : Sum n}{X : Setⁿ n}(C : Constr σ)
      → ⟦ σ ⟧S X → Maybe (⟦ typeOf σ C ⟧P X)
match C x with sop x
... | tag C₂ p with C ≟F C₂
... | yes refl = just p
... | no  _    = nothing

-- * Fixpoint

Fam : ℕ → Set
Fam n = Vec (Sum n) n

data Fix {n : ℕ}(φ : Fam n) : Fin n → Set where
  ⟨_⟩ : ∀{i} → ⟦ Vec-lookup i φ ⟧S (Fix φ) → Fix φ i

{-# TERMINATING #-}
_≟Fix_ : ∀{n i}{φ : Fam n} → (x y : Fix φ i) → Dec (x ≡ y)
_≟Fix_ {φ = φ} ⟨ sx ⟩ ⟨ sy ⟩ with DecEq._≟S_ (Fix φ) _≟Fix_ sx sy
... | yes refl = yes refl
... | no ¬p = no (λ { refl → ¬p refl })

