open import Digems.Prelude

-- Defines a higher order version of 'Any', indexed over
-- an 'All' instead of a simple list.
module Digems.Prelude.Any2 where

data Any2 {a p q}{A : Set a}{P : A → Set p}
          (Q : ∀{x} → P x → Set q) 
         : ∀{l} → All P l → Set (a ⊔ₗ p ⊔ₗ q) where
  here  : {x : A}{xs : List A}{p : P x}{ps : All P xs} 
        → Q {x} p → Any2 Q (p ∷ ps)
  there : {x : A}{xs : List A}{p : P x}{ps : All P xs}
        → Any2 Q ps
        → Any2 Q (p ∷ ps)
