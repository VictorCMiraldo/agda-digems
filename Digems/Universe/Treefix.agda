open import Digems.Prelude
open import Digems.Universe.Base

module Digems.Universe.Treefix {n : ℕ}(φ : Fam n) where

open DecEq (Fix φ) _≟Fix_

-- * Treefixes

data UTx {ℓ}(F : Atom n → Set ℓ) : Atom n → Set ℓ where
  hole : ∀{at} → F at   → UTx F at
  opq  : ∀{κ}  → ⟦ κ ⟧K → UTx F (K κ)
  peel : ∀{ι}  → (c : Constr' φ ι)
               → All (UTx F) (typeOf' φ ι c)
               → UTx F (I ι)

All-prop : ∀{ℓ₁ ℓ₂ a}{A : Set a}{xs : List A}{P : A → Set ℓ₁}
         → (∀{x} → P x → Set ℓ₂) → All P xs → Set ℓ₂
All-prop F []         = Unit
All-prop F (px ∷ all) = F px × All-prop F all

data TxProp {ℓ₁ ℓ₂}{F : Atom n → Set ℓ₁}(P : ∀{α} → F α → Set ℓ₂) 
          : ∀{α} → UTx F α → Set ℓ₂ where
  p-hole : ∀{at}{x : F at} → P x → TxProp P (hole x)
  p-opq  : ∀{κ}{k : ⟦ κ ⟧K} → TxProp P (opq k) 
  p-peel : ∀{ι}{c : Constr' φ ι}{xs : All (UTx F) (typeOf' φ ι c)}
         → All-prop (TxProp P) xs
         → TxProp P (peel c xs)

{-# TERMINATING #-}
txMap : ∀{ℓ₁ ℓ₂}{F : Atom n → Set ℓ₁}{G : Atom n → Set ℓ₂}
      → F ⊆ G → UTx F ⊆ UTx G
txMap tr (hole x)   = hole (tr x)
txMap tr (opq x)    = opq x
txMap tr (peel c x) = peel c (All-map (txMap tr) x)

txNotHole : ∀{ℓ F at} → UTx {ℓ} F at → Set
txNotHole (hole _)   = ⊥
txNotHole (opq _)    = Unit
txNotHole (peel _ _) = Unit

{-
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
-}

{-# TERMINATING #-}
txFold : ∀{ℓ₁ ℓ₂ F α}{G : Atom n → Set ℓ₂}
       → (∀{at} → F at → G at)
       → (∀{κ}  → ⟦ κ ⟧K → G (K κ))
       → (∀{ι}  → (c : Constr' φ ι) → All G (typeOf' φ ι c) → G (I ι))
       → (tx : UTx {ℓ₁} F α) → G α
txFold f-hole f-opq f-peel (hole x) = f-hole x
txFold f-hole f-opq f-peel (opq x) = f-opq x
txFold f-hole f-opq f-peel (peel c x)
  = f-peel c (All-map (txFold f-hole f-opq f-peel) x)

txFoldMon : ∀{ℓ₁ ℓ₂ F α}{G : Set ℓ₂}
          → (∀{at} → F at → G)
          → (∀{κ}  → ⟦ κ ⟧K → G)
          → (List G → G)
          → (tx : UTx {ℓ₁} F α) → G
txFoldMon {G = G} f-hole f-opq cat 
  = txFold {G = const G} f-hole f-opq (λ _ → cat ∘ All-fgt)

txJoin : ∀{ℓ F at} → UTx {ℓ} (UTx F) at → UTx F at
txJoin = txFold id opq peel

{-# TERMINATING #-}
txStiff : ∀{ℓ F ι} → Fix φ ι → UTx {ℓ} F (I ι)
txStiff {_} {F} ⟨ rep ⟩ with sop rep
...| tag c p = peel c (All-map (elimA {Y = UTx F} opq txStiff) p)


  
