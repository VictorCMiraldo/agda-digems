open import Digems.Prelude
open import Digems.Universe.Base using (Fam)

module Digems.Metatheory.Apply {n : ℕ}(φ : Fam n) where

 open import Digems.Universe φ
 
 module WithArity (arity : ℕ)(typeOfVar : Fin arity → Atom n) where
 
  import Digems.Metatheory.Patch 
  open Digems.Metatheory.Patch.WithArity φ arity typeOfVar

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

  txInj : ∀{α} → TermSubst → Tx α → Maybe ⟦ α ⟧A
  txInj σ = txFold {G = Maybe ∘ ⟦_⟧A} 
                   (λ { (v , refl) → σ v }) 
                   just 
                   (λ c xs → Maybe-map (⟨_⟩ ∘ inj c) 
                                       (All-Maybe-sequence xs))

  apply : ∀{α} → Patch α → ⟦ α ⟧A → Maybe ⟦ α ⟧A
  apply (patch d i wf) x with txMatch d x ∅ 
  ...| nothing = nothing 
  ...| just σ  = txInj σ i

{-
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
-}
