open import Digems.Prelude
open import Digems.Universe.Base

module Digems.Universe.Treefix {n : ℕ}(φ : Fam n) where

-- * Treefixes

data Tx {ℓ}(F : Atom n → Set ℓ) : Atom n → Set ℓ where
  hole : ∀{at} → F at   → Tx F at
  opq  : ∀{κ}  → ⟦ κ ⟧K → Tx F (K κ)
  peel : ∀{ι}  → (c : Constr' φ ι)
               → All (Tx F) (typeOf' φ ι c)
               → Tx F (I ι)

{-# TERMINATING #-}
txHoleIdxs : ∀{ℓ F at} → Tx {ℓ} F at → List (Atom n)
txHoleIdxs (hole {at} _) = at ∷ []
txHoleIdxs (opq _)       = []
txHoleIdxs (peel _ a)    = concat (All-fgt (All-map txHoleIdxs a))

{-# TERMINATING #-}
txHoles : ∀{ℓ F at}(tx : Tx {ℓ} F at) → All F (txHoleIdxs tx)
txHoles (hole x)    = x ∷ []
txHoles (opq _)     = []
txHoles {F = F} (peel _ ps) 
  = aux ps
  where
    aux : ∀{ℓ F as} 
        → (π : All (Tx {ℓ} F) as)
        → All F (concat (All-fgt (All-map txHoleIdxs π)))
    aux []       = []
    aux (p ∷ ps) = All-++ (txHoles p) (aux ps)

{-# TERMINATING #-}
txJoin : ∀{ℓ F at} → Tx {ℓ} (Tx F) at → Tx F at
txJoin (hole x)     = x
txJoin (opq k)      = opq k
txJoin (peel c txs) = peel c (All-map txJoin txs) 

{-# TERMINATING #-}
txStiff : ∀{ℓ F ι} → Fix φ ι → Tx {ℓ} F (I ι)
txStiff {_} {F} ⟨ rep ⟩ with sop rep
...| tag c p = peel c (All-map (elimA {Y = Tx F} opq txStiff) p)
