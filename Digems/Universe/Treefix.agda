open import Digems.Prelude
open import Digems.Universe.Base

module Digems.Universe.Treefix {n : ℕ}(φ : Fam n) where

-- * Treefix indexes

data Txᵢ : Set where
  holeᵢ : Atom n → Txᵢ
  pellᵢ : List Txᵢ → Txᵢ


-- * Treefixes

data Tx {a}(F : Atom n → Set a) : Atom n → Set a where
  hole : ∀{at} → F at   → Tx F at
  opq  : ∀{κ}  → ⟦ κ ⟧K → Tx F (K κ)
  peel : ∀{ι}  → (c : Constr' φ ι)
               → All (Tx F) (typeOf' φ ι c)
               → Tx F (I ι)

{-# TERMINATING #-}
txHoles : ∀{a F at} → Tx {a} F at → List (Atom n)
txHoles (hole {at} _) = at ∷ []
txHoles (opq _)       = []
txHoles (peel _ a)    = concat (All-fgt (All-map txHoles a))

{-# TERMINATING #-}
txJoin : ∀{a F at} → Tx {a} (Tx F) at → Tx F at
txJoin (hole x)     = x
txJoin (opq k)      = opq k
txJoin (peel c txs) = peel c (All-map txJoin txs) 


