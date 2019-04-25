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
  
  TxVar : Atom n → Set
  TxVar α = Σ (Fin arity) (λ f → α ≡ typeOfVar f)

  Tx : Atom n → Set
  Tx = UTx TxVar

  TxSubst : Set
  TxSubst = (v : Fin arity) → Tx (typeOfVar v)
 
  TermSubst : Set
  TermSubst = (v : Fin arity) → Maybe (⟦ typeOfVar v ⟧A (Fix φ))

  ∅ : TermSubst
  ∅ _ = nothing

  _↦_ : (v : Fin arity) → ⟦ typeOfVar v ⟧A (Fix φ)
      → TermSubst → TermSubst
  (v ↦ el) σ v' with v ≟F v'
  ...| yes refl = just el
  ...| no  _    = σ v'
  
  insert : (v : Fin arity) → ⟦ typeOfVar v ⟧A (Fix φ) 
         → TermSubst → Maybe TermSubst
  insert v el σ with σ v
  ...| nothing = just ((v ↦ el) σ)
  ...| just el' with _≟A_ {typeOfVar v} el el'
  ...| yes _ = just σ
  ...| no  _ = nothing



  
