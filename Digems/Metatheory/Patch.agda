open import Digems.Prelude
open import Digems.Universe.Base using (Fam)

module Digems.Metatheory.Patch {n : ℕ}(φ : Fam n) where

 open import Digems.Universe φ
 
 module WithArity (arity : ℕ)(typeOfVar : Fin arity → Atom n) where

  open import Digems.Universe.Treefix φ public

  TxVar : Atom n → Set
  TxVar α = Σ (Fin arity) (λ f → α ≡ typeOfVar f)

  Tx : Atom n → Set
  Tx = UTx TxVar

  TxSubst : Set
  TxSubst = (v : Fin arity) → Tx (typeOfVar v)
 
  TermSubst : Set
  TermSubst = (v : Fin arity) → Maybe (⟦ typeOfVar v ⟧A)

  ∅ : TermSubst
  ∅ _ = nothing

  _↦_ : (v : Fin arity) → ⟦ typeOfVar v ⟧A
      → TermSubst → TermSubst
  (v ↦ el) σ v' with v ≟F v'
  ...| yes refl = just el
  ...| no  _    = σ v'

  insert : (v : Fin arity) → ⟦ typeOfVar v ⟧A
         → TermSubst → Maybe TermSubst
  insert v el σ with σ v
  ...| nothing = just ((v ↦ el) σ)
  ...| just el' with _≟A_ {typeOfVar v} el el'
  ...| yes _ = just σ
  ...| no  _ = nothing

  -- Which variables appear in a 'Tx'?

  v∅ : Vec Bool arity
  v∅ = Vec-replicate false

  set-bit : ∀{α} → TxVar α → Vec Bool arity
  set-bit (idx , _) = Vec-updateAt idx (const true) v∅

  and* : List (Vec Bool arity) → Vec Bool arity
  and* []       = v∅
  and* (x ∷ xs) = Vec-zipWith _∧_ x (and* xs)

  txVars : ∀{α} → Tx α → Vec Bool arity
  txVars = txFoldMon set-bit (const v∅) and*

  record Patch (α : Atom n) : Set where
    constructor patch
    field
      del : Tx α
      ins : Tx α
      wf  : txVars del ≡ txVars ins
