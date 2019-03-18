open import Digems.Prelude
open import Digems.Universe.Base

-- We shall carry out the proof that our ordering of
-- relevant treefixes is, in fact, a preorder.
module Digems.Universe.Treefix.Preorder {n : ℕ}(φ : Fam n) where

open import Digems.Universe.Treefix φ
  renaming (Tx to Treefix)
open DecEq (Fix φ) _≟Fix_

-- The first abstraction is that we shall fix the number of metariables.
-- This, in fact, produces a family of proofs. Each for a treefix with
-- a given number of variables. Note that since treefixes might not
-- use all its variables, we just care for the treefix with *the most* variables.
module WithArity (arity : ℕ) where

 MetaVar : Atom n → Set
 MetaVar α = Fin arity

 Tx : Atom n → Set
 Tx = Treefix MetaVar

 -- We define a substitution to be a vector assigning to each metavariable
 -- a treefix.
 SubstN : ℕ → Set
 -- SubstN = Vec (Maybe (Σ (Atom n) (λ α → ⟦ α ⟧A (Fix φ))))
 SubstN = Vec (Maybe (Σ (Atom n) Tx))

 {-# TERMINATING #-}
 fromEl : ∀{α} → ⟦ α ⟧A (Fix φ) → Tx α
 fromEl {I ι} (⟨ x ⟩) with sop x
 ...| tag c p = peel c (All-map {!fromEl!} p)
 fromEl {K κ} k     = opq k

 -- Two substitutions are compatible iff they assime the same terms to the
 -- same metavariables.
 Compatible : ∀{n} → SubstN n → SubstN n → Set
 Compatible [] [] = Unit
 Compatible (nothing         ∷ σ₁) (just (α₂ , tx₂) ∷ σ₂) = Compatible σ₁ σ₂
 Compatible (nothing         ∷ σ₁) (nothing         ∷ σ₂) = Compatible σ₁ σ₂
 Compatible (just (α₁ , tx₁) ∷ σ₁) (nothing         ∷ σ₂) = Compatible σ₁ σ₂
 Compatible (just (α₁ , tx₁) ∷ σ₁) (just (α₂ , tx₂) ∷ σ₂) 
   = Σ (α₁ ≡ α₂) (λ { refl → tx₁ ≡ tx₂ }) × Compatible σ₁ σ₂

 -- When substitutions are compatible, we can join them.
 subst-join : ∀{n}(σ₁ σ₂ : SubstN n)(hip : Compatible σ₁ σ₂) → SubstN n
 subst-join []                     []     unit       = []
 subst-join (nothing ∷ σ₁) (just s₂ ∷ σ₂) hip        = just s₂ ∷ subst-join σ₁ σ₂ hip
 subst-join (nothing ∷ σ₁) (nothing ∷ σ₂) hip        = nothing ∷ subst-join σ₁ σ₂ hip
 subst-join (just s₁ ∷ σ₁) (nothing ∷ σ₂) hip        = just s₁ ∷ subst-join σ₁ σ₂ hip
 subst-join (just s₁ ∷ σ₁) (just s₂ ∷ σ₂) (h₀ , hip) = just s₁ ∷ subst-join σ₁ σ₂ hip

 -- empty substitution
 subst-empty : ∀{n} → SubstN n
 subst-empty {zero}  = []
 subst-empty {suc n} = nothing ∷ subst-empty

 -- predicate that ensures that the image of 'idx' under 'σ' is proositionally
 -- equal to 'tx'
 subst-img-is : ∀{n α}(σ : SubstN n)(idx : Fin n)(tx : Tx α) → Set
 subst-img-is {_} {α} σ idx tx with Vec-lookup idx σ
 ...| nothing         = ⊥
 ...| just (α' , tx') 
   with α ≟Atom α'
 ...| no _     = ⊥
 ...| yes refl = tx ≡ tx'

 -- Finally, a substitution associates one 'tx' to each variable.
 Subst : Set
 Subst = SubstN arity

 -- The patches we wish to compare are elements of Dₓʸ,
 -- defined by the set of patches p s.t. apply p x ≡ just y.
 -- Working under the same substitution provides an easier way
 -- of carrying this hypothesis around. We must compare patches
 -- under a substitution and a proof that exhaustively applying that
 -- substitution yields x.
 module Under (σ : Subst) where

  -- We define our order paramtrized by a substitution
  -- from variables to terms.
  mutual
    data Tx≤* : ∀{π}(p q : All Tx π) → Set where
      Tx≤[] : Tx≤* [] []
      Tx≤∷  : ∀{α π}{p q : Tx α}{ps qs : All Tx π}
            → Tx≤ p q 
            → Tx≤* ps qs 
            → Tx≤* (p ∷ ps) (q ∷ qs) 

    data Tx≤ : ∀{α}(p q : Tx α) → Set where

      Tx≤Refl  : ∀{α}{d : Tx α} → Tx≤ d d

      Tx≤Peel  : ∀{ι}(c : Constr' φ ι){ps qs : All Tx (typeOf' φ ι c)}
               → Tx≤* ps qs
               → Tx≤ (peel {ι = ι} c ps) (peel c qs)

      Tx≤Subst : ∀{at idx}{t : Tx at}
               → subst-img-is σ idx t
               → Tx≤ t (hole {at = at} idx)

  Tx≤-refl : ∀{α}(p : Tx α) → Tx≤ p p
  Tx≤-refl p = Tx≤Refl

  

{-
  Tx≤-trans : ∀{α}{p q r : Tx α} → Tx≤ p q → Tx≤ q r → Tx≤ p r
  Tx≤-trans Tx≤Refl        qr = qr
  Tx≤-trans (Tx≤Subst prf) Tx≤Refl = Tx≤Subst prf
  Tx≤-trans (Tx≤Subst {idx = idx₀} prf) (Tx≤Subst {idx = idx'} prf') 
    with idx₀ ≟F idx'
  ...| no abs = Tx≤Subst {!!}
  ...| yes refl = Tx≤Refl
  Tx≤-trans (Tx≤Subst prf) (Tx≤Subst prf') 
    = Tx≤Subst {!!}
  Tx≤-trans pq      qr = {!!}
-}

{-
 -- We are only interested in transitivity for 
 module _ (WithCommonDomain : (σ₁ σ₂ : Subst) → Compatible σ₁ σ₂) where 


-- Here we are only handling treefixes with 
-- natural numbers as metavariables. We can try
-- to generalize later.


data TxD {ℓ}(F : Atom n → Set ℓ) : Atom n → Set ℓ where
  hole  : ∀{at} → F at   → TxD F at
  under : ∀{at}          → TxD F at
  peel  : ∀{ι}  → (c : Constr' φ ι)
                → All (TxD F) (typeOf' φ ι c)
                → TxD F (I ι)
-}
{-
Subst : Set
Subst = ∀{α} → MetaVar α → Maybe (Tx' α)

subst1 : ∀{α} → MetaVar α → Tx' α → Subst
subst1 {α} n x {α'} n' 
  with α ≟Atom α'
...| no _ = nothing
...| yes refl
  with n ≟N n'
...| no  _ = nothing
...| yes _ = just x

Matches : ∀{α} → Tx' α → ⟦ φ ⟧FA α → Maybe Subst
Matches {α} (hole x) el = just (subst1 {α} x (fromEl el))
Matches under el        = just (const nothing)
Matches (peel c x) el   = {!!}
-}

{-
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
-} 

    
{-
-- Finally, the final relation between Tx's
_⊑_ : ∀{at} → Tx' at → Tx' at → Set
p ⊑ q = Σ Subst (λ σ → Tx≤ σ p q)
-}

-- Now, the fun part! Proving it is a preorder!

{-
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
-}

-- When proving transitivity, we are given two substitutions;
--
-- One that witnesses p ⊑ q, call it σ₁ and another
-- that witnesses q ⊑ r, call it σ₂.
--
-- If nothing else is said, σ₁ and σ₂ might disagree. That is,
-- σ₁ n ≡ just t ≢ just t' ≡ σ₂ n. Upon closer inspection, however,
-- we see this cannot happen. Both p , q and r transform a fixed x into a 
-- fixed y. Hence, the witnesses of p ⊑ q and q ⊑ r must agree.
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
