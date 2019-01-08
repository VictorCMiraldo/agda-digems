open import Digems.Prelude
open import Digems.Universe.Base

module Digems.Universe.Treefix.PreoderInst where

bintree : Fam 1
bintree = ([] ∷ (I zero ∷ I zero ∷ []) ∷ []) ∷ []

open import Digems.Universe.Treefix bintree
  renaming (Tx to Treefix)
open import Digems.Universe.Treefix.Preorder bintree

open WithArity 2

tx1 : Tx (I zero)
tx1 = peel (suc zero) ((hole zero) ∷ (hole (suc zero)) ∷ [])

tx2 : Tx (I zero)
tx2 = peel (suc zero) (hole zero ∷ hole zero ∷ [])

test : Tx≤ (nothing ∷ just (I zero , hole zero) ∷ []) tx2 tx1 
test = Tx≤Peel (suc zero) 
               (Tx≤∷ Tx≤Refl 
               (Tx≤∷ (Tx≤Subst refl) 
                     Tx≤[]))

test2 : Tx≤ (just (I zero , hole (suc zero)) ∷ nothing ∷ []) tx1 tx2
test2 = Tx≤Peel (suc zero)
                (Tx≤∷ Tx≤Refl 
                (Tx≤∷ (Tx≤Subst refl) 
                 Tx≤[])) 
