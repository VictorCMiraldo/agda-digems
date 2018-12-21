open import Digems.Prelude
open import Digems.Universe.Base

module Digems.Universe.Treefix.Preorder {n : ℕ}(φ : Fam n) where

open import Digems.Universe.Treefix φ

-- Here we are only handling treefixes with 
-- natural numbers as metavariables. We can try
-- to generalize later.

MetaVar : Atom n → Set
MetaVar α = ℕ

Tx' : Atom n → Set
Tx' = Tx MetaVar

Subst : Set
Subst = ∀{α} → MetaVar α → Maybe (Tx' α)

-- We define our order paramtrized by a substitution
-- from variables to terms.
mutual
  data Tx≤* (σ : Subst)
           : ∀{π}(p q : All Tx' π) → Set where
    Tx≤[] : Tx≤* σ [] []
    Tx≤∷  : ∀{α π}(p q : Tx' α)(ps qs : All Tx' π)
          → Tx≤ σ p q
          → Tx≤* σ ps qs
          → Tx≤* σ (p ∷ ps) (q ∷ qs)

  data Tx≤ (σ : Subst)
           : ∀{α}(p q : Tx' α) → Set where

    Tx≤KonKon  : ∀{κ}(k : ⟦ κ ⟧K)   → Tx≤ σ (opq k) (opq k)
    Tx≤KonHole : ∀{κ n}(k : ⟦ κ ⟧K) → Tx≤ σ (opq k) (hole n)

    Tx≤Peel  : ∀{ι}(c : Constr' φ ι)(ps qs : All Tx' (typeOf' φ ι c))
             → Tx≤* σ ps qs
             → Tx≤ σ (peel {ι = ι} c ps) (peel c qs)

    Tx≤Var   : ∀{at}{n : ℕ}
             → Tx≤ σ (hole {at = at} n) (hole n)
 
    Tx≤Subst : ∀{at}{n : ℕ}{t : Tx' at}
             → σ n ≡ just t
             → Tx≤ σ t (hole {at = at} n)

-- We can give an extensional charaterization of Tx≤
-- by the means of a non-deterministic apply function
module _ where
 
  -- bring in the list monad into scope 
  open import Data.List.Categorical using (monadPlus)
  open RawMonadPlus {f = lz} monadPlus

  applySubst* : ∀{π} → Subst → All Tx' π → List (All Tx' π)

  applySubst : ∀{α} → Subst → Tx' α → List (Tx' α)
  applySubst σ (opq k)     = return (opq k)
  applySubst {α} σ (hole n) with σ {α} n 
  ...| nothing = return (hole n)
  ...| just t  = return t 
               ∣ return (hole n)
  applySubst σ (peel c ps) = peel c <$> (applySubst* σ ps)
  
  applySubst* σ [] = return []
  applySubst* σ (p ∷ ps) = applySubst σ p >>= λ p' 
                         → (p' ∷_) <$> applySubst* σ ps
  

    

-- Finally, the final relation between Tx's
_⊑_ : ∀{at} → Tx' at → Tx' at → Set
p ⊑ q = Σ Subst (λ σ → Tx≤ σ p q)

-- Now, the fun part! Proving it is a preorder!

-- Reflexivity is trivial!
⊑-refl : ∀{at}(p : Tx' at) → p ⊑ p
⊑-refl p = const nothing , go p
  where
    aux : ∀{π} → (x : All Tx' π) → Tx≤* (const nothing) x x

    go : ∀{at}(p : Tx' at) → Tx≤ (const nothing) p p
    go (hole x)   = Tx≤Var
    go (opq x)    = Tx≤KonKon x
    go (peel c x) = Tx≤Peel c x x (aux x)

    aux []       = Tx≤[]
    aux (x ∷ xs) = Tx≤∷ x x xs xs (go x) (aux xs)


{-
postulate
  patches-disagree : ∀{a}{A : Set a} → A
  malformed-subst  : ∀{a}{A : Set a} → A


⊑-trans : ∀{at}{p q r : Tx' at}(pq : p ⊑ q)(qr : q ⊑ r)
        → p ⊑ r
⊑-trans (σ₁ , pq) (σ₂ , qr) = {!!} , go σ₁ σ₂ pq qr
  where
{-
    go : ∀{at}(σ₁ σ₂ : Subst){p q r : Tx' at}
       → Tx≤ σ₁ p q → Tx≤ σ₂ q r → Tx≤ σ₁ p r
    go σ₁ σ₂ {r = opq k'} (Tx≤Kon k) (Tx≤Kon .k')
     = Tx≤Kon k
    go {K κ} σ₁ σ₂ {r = hole n} (Tx≤Kon k) qr
     with σ₁ {K κ} n | inspect (σ₁ {K κ}) n
    ...| opq k'  | [ R ] = {!!}
    ...| hole n' | [ R ] = {!!}
    go σ₁ σ₂ _ _ = {!!}
-}
    go : ∀{at}(σ₁ σ₂ : Subst){p q r : Tx' at}
       → Tx≤ σ₁ p q → Tx≤ σ₂ q r → Tx≤ σ₂ p r
    go σ₁ σ₂ {r = opq k'} (Tx≤KonKon k) (Tx≤KonKon .k')
     = Tx≤KonKon k
    go {K κ} σ₁ σ₂ {r = hole n} (Tx≤KonKon k) qr
     = Tx≤KonHole k
    go {K k} σ₁ σ₂ {r = hole n} (Tx≤Var {n = n'}) qr = qr
    go {I ι} σ₁ σ₂ {r = hole n} (Tx≤Var {n = n'}) qr = qr
    go {I ι} σ₁ σ₂ {r = hole n} (Tx≤Peel c ps qs pq) qr 
      with σ₂ {I ι} n
    ...| r = {!!}
{-
     with σ₂ {K κ} n | inspect (σ₂ {K κ}) n
    ...| opq k' | [ R ] with k ≟K k'
    ...| yes refl rewrite sym R = Tx≤Subst
    ...| no  _    = patches-disagree
    go {K κ} σ₁ σ₂ {r = hole n} (Tx≤KonKon k) qr | hole n' | [ R ] 
       = {!!}
-}
    go σ₁ σ₂ _ _ = {!!}
-}
