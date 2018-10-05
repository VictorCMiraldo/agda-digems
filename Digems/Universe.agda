open import Digems.Prelude
open import Digems.Universe.Family

-- The actual modeling of the algorithm
-- only uses generic functions modulo a given family.
--
-- This module defines a bunch of helpful renamings
-- and passing of default arguments.
module Digems.Universe {n : ℕ}(φ : Fam n) where

open import Digems.Universe.Base
  using ( Atom ; K ; I ; Prod ; Sum 
        ; Fix ; ⟨_⟩ ; _≟Fix_
        ; inj ; match 
        ; sop ; SOP ; tag
        )
  public
open import Digems.Universe.Opaque
  public

import Digems.Universe.Base as Base
open Base.DecEq (Fix φ) _≟Fix_ public

-- Interpretation of atoms, products and sums 
-- over the family
⟦_⟧A : Atom n → Set
⟦ a ⟧A = Base.⟦_⟧A a (Fix φ) 

⟦_⟧P : Prod n → Set
⟦ p ⟧P = Base.⟦_⟧P p (Fix φ) 

⟦_⟧S : Sum n → Set
⟦ s ⟧S = Base.⟦_⟧S s (Fix φ) 

-- Element of the family
El : Fin n → Set
El = Fix φ

-- Constructors for an element in the family
Constr : Fin n → Set
Constr = Base.Constr' φ

-- Type of a constructor of the family
typeOf : (ι : Fin n) → Constr ι → Prod n
typeOf = Base.typeOf' φ
