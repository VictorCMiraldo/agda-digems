open import Digems.Prelude
open import Digems.Universe.Family

module Digems.Diff.Types {n : ℕ}(φ : Fam n) where

open import Digems.Universe φ
open import Digems.Universe.Treefix φ
open import Digems.Universe.Subtree φ

Γ : ℕ → Set
Γ = Vec (Atom n)

data MetaVarIK {m : ℕ}(ctx : Γ m) : Atom n → Set where
  var : (i : Fin m) → MetaVarIK ctx (Vec-lookup i ctx)

record Change (at : Atom n) : Set where
  constructor change
  field 
    arity  : ℕ
    decls  : Γ arity
    delCtx : Tx (MetaVarIK decls) at
    insCtx : Tx (MetaVarIK decls) at

Patch : Atom n → Set
Patch = Tx Change
  
-- common subtree map of two trees
CSM : ∀{ι}(src dst : Fix φ ι) → Set
CSM src dst = ∀{ν} 
            → (tgt : Fix φ ν)
            → Maybe (tgt ⊆Fix src × tgt ⊆Fix dst)
