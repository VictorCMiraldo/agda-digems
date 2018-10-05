open import Digems.Prelude
open import Digems.Prelude.Any2
open import Digems.Universe.Base

module Digems.Universe.Location {n : ℕ}(φ : Fam n) where

-- Defines a location inside a value of type α
data Loc : Atom n → Set where
  here  : ∀{α} → Loc α
  there : ∀{ν}(c : Constr' φ ν)
        → Any Loc (typeOf' φ ν c)
        → Loc (I ν)

data _Loc∈_ : {α : Atom n} → Loc α → ⟦ α ⟧A (Fix φ) → Set where
  here  : ∀{α}{a : ⟦ α ⟧A (Fix φ)} → _Loc∈_ {α} here a
  there : ∀{ν}(c : Constr' φ ν)
        → {p : ⟦ typeOf' φ ν c ⟧P (Fix φ)}
        → (l : Any Loc (typeOf' φ ν c))
        → {!!}
        → (there {ν} c l) Loc∈ ⟨ inj c p ⟩
  

