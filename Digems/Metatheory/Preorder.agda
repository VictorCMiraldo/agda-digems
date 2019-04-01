open import Digems.Prelude
open import Digems.Universe.Base

-- We shall carry out the proof that our ordering of
-- relevant treefixes is, in fact, a preorder.
module Digems.Metatheory.Preorder {n : ℕ}(φ : Fam n) where

 open DecEq (Fix φ) _≟Fix_
 
 -- The first abstraction is that we shall fix the number of metariables.
 -- This, in fact, produces a family of proofs. Each for a treefix with
 -- a given number of variables. Note that since treefixes might not
 -- use all its variables, we just care for the treefix with *the most* variables.
 module WithArity (arity : ℕ)(typeOfVar : Fin arity → Atom n) where
 
  open import Digems.Universe.Treefix φ
  open WellTyped arity typeOfVar

  module Under (σ : Subst) where
 
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
 
       Tx≤Subst : ∀{idx}{p : Tx (typeOfVar idx)}
                → txNotHole p
                → Tx≤ p (σ idx)
                → Tx≤ p (hole (idx , refl))
 
   Tx≤*-refl : ∀{π}{ps : All Tx π} → Tx≤* ps ps
   Tx≤*-refl {ps = []}     = Tx≤[]
   Tx≤*-refl {ps = p ∷ ps} = Tx≤∷ Tx≤Refl Tx≤*-refl

   Tx≤-nh : ∀{α}{p q : Tx α} → Tx≤ p q → txNotHole q → txNotHole p
   Tx≤-nh Tx≤Refl hip = hip
   Tx≤-nh (Tx≤Peel c x) hip = unit
   Tx≤-nh (Tx≤Subst x prf) ()
 
   mutual
    Tx≤*-trans : ∀{π}{p q r : All Tx π} → Tx≤* p q → Tx≤* q r → Tx≤* p r
    Tx≤*-trans pq Tx≤[] = pq
    Tx≤*-trans (Tx≤∷ a as) (Tx≤∷ b bs) = Tx≤∷ (Tx≤-trans a b) (Tx≤*-trans as bs)
  
    Tx≤-trans : ∀{α}{p q r : Tx α} → Tx≤ p q → Tx≤ q r → Tx≤ p r
    Tx≤-trans pq Tx≤Refl = pq
    Tx≤-trans Tx≤Refl (Tx≤Peel c x) = Tx≤Peel c (Tx≤*-trans Tx≤*-refl x)
    Tx≤-trans (Tx≤Peel .c x₁) (Tx≤Peel c x) = Tx≤Peel c (Tx≤*-trans x₁ x)
    Tx≤-trans {q = q} pq (Tx≤Subst {idx = v} prf rec) = Tx≤Subst (Tx≤-nh pq prf) (Tx≤-trans pq rec)

{-
module TestDrive where
  
  Fam-Bin : Fam 1
  Fam-Bin = ((I zero ∷ I zero ∷ []) ∷ [] ∷ []) ∷ []

  open ForFam Fam-Bin
  open WithArity 3 (λ _ → I zero)

  postulate σ : Subst
  postulate σ-nz : not-hole (σ zero)

  open Under σ

  better : Tx (I zero) 
  better = peel zero (hole zero ∷ hole zero ∷ [])

  worse : Tx (I zero)
  worse = peel zero (hole zero ∷ σ zero ∷ [])

  w≤b : Tx≤ worse better
  w≤b = Tx≤Peel zero (Tx≤∷ Tx≤Refl (Tx≤∷ (Tx≤Subst σ-nz Tx≤Refl) Tx≤[]))

-}
