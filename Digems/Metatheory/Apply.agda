open import Digems.Prelude
open import Digems.Universe.Base using (Fam)

-- We shall carry out the proof that our ordering of
-- relevant treefixes is, in fact, a preorder.
module Digems.Metatheory.Apply {n : ℕ}(φ : Fam n) where

 open import Digems.Universe φ
 
 -- The first abstraction is that we shall fix the number of metariables.
 -- This, in fact, produces a family of proofs. Each for a treefix with
 -- a given number of variables. Note that since treefixes might not
 -- use all its variables, we just care for the treefix with *the most* variables.
 module WithArity (arity : ℕ)(typeOfVar : Fin arity → Atom n) where
 
  open import Digems.Universe.Treefix φ
  open WellTyped arity typeOfVar

  txMatch* : ∀{π} → All Tx π → ⟦ π ⟧P → TermSubst → Maybe TermSubst

  txMatch : ∀{α} → Tx α → ⟦ α ⟧A → TermSubst → Maybe TermSubst
  txMatch (opq x) a σ with a ≟K x 
  ...| yes _ = just σ
  ...| no  _ = nothing
  txMatch (hole (var , refl)) a σ = insert var a σ
  txMatch (peel c x) ⟨ a ⟩ σ with match c a
  ...| nothing = nothing
  ...| just as = txMatch* x as σ

  txMatch* [] [] σ = just σ
  txMatch* (tx ∷ txs) (a ∷ as) σ with txMatch tx a σ
  ...| nothing = nothing
  ...| just σ' = txMatch* txs as σ'

  Is-just : ∀{a}{A : Set a} → Maybe A → Set
  Is-just (just _) = Unit
  Is-just nothing  = ⊥

  is-def : TermSubst → ∀{α} → TxVar α → Set
  is-def σ (v , _) = Is-just (σ v)

  txMatch*-complete 
    : ∀{π}{as : ⟦ π ⟧P}{σ σ' : TermSubst}(txs : All Tx π)
    → txMatch* txs as σ ≡ just σ'
    → All-prop (TxProp (is-def σ')) txs

  txMatch-complete 
    : ∀{α}{a : ⟦ α ⟧A}{σ σ' : TermSubst}(tx : Tx α)
    → txMatch tx a σ ≡ just σ'
    → TxProp (is-def σ') tx
  txMatch-complete (hole (x , refl)) h = p-hole {!!}
  txMatch-complete (opq x) h    = p-opq
  txMatch-complete {a = ⟨ a ⟩} (peel c x) h with match c a
  ...| nothing = ⊥-elim {!!}
  ...| just as = p-peel (txMatch*-complete x h)
    
  txMatch*-complete [] hip = unit
  txMatch*-complete {as = a ∷ as} {σ = σ₀} (px ∷ txs) hip 
    with txMatch px a σ₀ | inspect (txMatch px a) σ₀
  ...| nothing | _     = ⊥-elim {!!}
  ...| just σ  | [ R ] = txMatch-complete {a = a} {σ = σ₀} px {!R!} , {!!}
