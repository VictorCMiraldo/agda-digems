open import Digems.Prelude
open import Digems.Prelude.Any2
open import Digems.Universe.Family

module Digems.Universe.Location {n : ℕ}(φ : Fam n) where

open import Digems.Universe φ

-- Defines a location inside a value of type α
data Loc : Atom n → Set where
  here  : ∀{α} → Loc α
  there : ∀{ν}(c : Constr ν)
        → Any Loc (typeOf ν c)
        → Loc (I ν)

data _Loc∈_ : {α : Atom n} → Loc α → ⟦ α ⟧A → Set where
  here  : ∀{α}{a : ⟦ α ⟧A} → _Loc∈_ {α} here a
  there : ∀{ν}(c : Constr ν)
        → {p : ⟦ typeOf ν c ⟧P}
        → (l : Any Loc (typeOf ν c))
        → AnyAllCurry _Loc∈_ l p
        → (there {ν} c l) Loc∈ ⟨ inj c p ⟩
  

