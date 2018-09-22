open import Digems.Prelude
open import Digems.Prelude.Any2
open import Digems.Universe.Base

module Digems.Universe.Subtree {n : ℕ}(φ : Fam n) where

mutual
  data _⊆A_ {ι}(x : Fix φ ι) : ∀{α} → ⟦ α ⟧A (Fix φ) → Set where
    suba : ∀{ν}{y : Fix φ ν}
         → x ⊆Fix y
         → _⊆A_ x {I ν} y

  data _⊆Fix_ {ι}(x : Fix φ ι) : ∀{ν} → Fix φ ν → Set where
    here  : x ⊆Fix x
    there : ∀{ν}(c : Constr' φ ν)
          → (np : ⟦ typeOf' φ ν c ⟧P (Fix φ)) 
          → Any2 (λ {α} → _⊆A_ x {α}) np
          → _⊆Fix_ x {ν} ⟨ inj c np ⟩
