open import Digems.Prelude
open import Digems.Universe.Base using (Fam ; I; Constr')

module Digems.Examples.2-3-Tree where

  fam : Fam 1
  fam = ((I zero ∷ I zero ∷ []) 
       ∷ (I zero ∷ I zero ∷ I zero ∷ []) 
       ∷ [] 
      ∷ []) ∷ []

  open import Digems.Universe fam hiding (I)

  2-3-tree : Set
  2-3-tree = ⟦ I zero ⟧A

  leaf : 2-3-tree
  leaf = ⟨ there (there (here [])) ⟩

  2-node : 2-3-tree → 2-3-tree → 2-3-tree
  2-node x y = ⟨ here (x ∷ y ∷ []) ⟩

  3-node : 2-3-tree → 2-3-tree → 2-3-tree → 2-3-tree
  3-node x y z = ⟨ there (here (x ∷ y ∷ z ∷ [])) ⟩

  cmp : 2-3-tree → 2-3-tree → Bool
  cmp x y with x ≟Fix y
  ...| yes _ = true
  ...| no  _ = false

  cmpM : 2-3-tree → Maybe 2-3-tree → Bool
  cmpM t nothing  = false
  cmpM t (just u) = cmp t u

  arity : ℕ
  arity = 4
 
  typeOfVar : Fin arity → Atom 1
  typeOfVar _ = I zero

  import Digems.Metatheory.Patch
  import Digems.Metatheory.Apply 

  open Digems.Metatheory.Patch.WithArity fam arity typeOfVar
  open Digems.Metatheory.Apply.WithArity fam arity typeOfVar

  v0 v1 v2 v3 : Tx (I zero)

  v0 = hole (zero , refl)
  v1 = hole (suc zero , refl)
  v2 = hole (suc (suc zero) , refl)
  v3 = hole (suc (suc (suc zero)) , refl)
  
  2-node' 3-node' : Constr' fam zero

  2-node' = zero
  3-node' = suc zero

  ------------------------------------------
  ------------------------------------------
  -- Patches
  ------------------------------------------
  ------------------------------------------

  p0 : Patch (I zero)
  p0 = patch (peel 2-node' (v0 ∷ v1 ∷ [])) 
             (peel 2-node' (v1 ∷ v0 ∷ []))
             refl

  t : Maybe 2-3-tree
  t = apply p0 (2-node (2-node leaf leaf) leaf)
  
