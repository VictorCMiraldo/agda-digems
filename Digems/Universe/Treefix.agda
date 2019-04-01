open import Digems.Prelude
open import Digems.Universe.Base

module Digems.Universe.Treefix {n : ℕ}(φ : Fam n) where

-- * Treefixes

data UTx {ℓ}(F : Atom n → Set ℓ) : Atom n → Set ℓ where
  hole : ∀{at} → F at   → UTx F at
  opq  : ∀{κ}  → ⟦ κ ⟧K → UTx F (K κ)
  peel : ∀{ι}  → (c : Constr' φ ι)
               → All (UTx F) (typeOf' φ ι c)
               → UTx F (I ι)

txNotHole : ∀{ℓ F at} → UTx {ℓ} F at → Set
txNotHole (hole _)   = ⊥
txNotHole (opq _)    = Unit
txNotHole (peel _ _) = Unit

{-# TERMINATING #-}
txHoleIdxs : ∀{ℓ F at} → UTx {ℓ} F at → List (Atom n)
txHoleIdxs (hole {at} _) = at ∷ []
txHoleIdxs (opq _)       = []
txHoleIdxs (peel _ a)    = concat (All-fgt (All-map txHoleIdxs a))

{-# TERMINATING #-}
txHoles : ∀{ℓ F at}(tx : UTx {ℓ} F at) → All F (txHoleIdxs tx)
txHoles (hole x)    = x ∷ []
txHoles (opq _)     = []
txHoles {F = F} (peel _ ps) 
  = aux ps
  where
    aux : ∀{ℓ F as} 
        → (π : All (UTx {ℓ} F) as)
        → All F (concat (All-fgt (All-map txHoleIdxs π)))
    aux []       = []
    aux (p ∷ ps) = All-++ (txHoles p) (aux ps)

{-# TERMINATING #-}
txJoin : ∀{ℓ F at} → UTx {ℓ} (UTx F) at → UTx F at
txJoin (hole x)     = x
txJoin (opq k)      = opq k
txJoin (peel c txs) = peel c (All-map txJoin txs) 

{-# TERMINATING #-}
txStiff : ∀{ℓ F ι} → Fix φ ι → UTx {ℓ} F (I ι)
txStiff {_} {F} ⟨ rep ⟩ with sop rep
...| tag c p = peel c (All-map (elimA {Y = UTx F} opq txStiff) p)

-- We also provide a 'well-typed' treefix abstraction over
-- an arbitrary number of variables.
module WellTyped (arity : ℕ)(typeOfVar : Fin arity → Atom n) where
  
  Tx : Atom n → Set
  Tx = UTx (λ α → Σ (Fin arity) (λ f → α ≡ typeOfVar f))

  Subst : Set
  Subst = (v : Fin arity) → Tx (typeOfVar v)
 

  
