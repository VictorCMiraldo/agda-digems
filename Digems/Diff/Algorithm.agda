open import Digems.Prelude
open import Digems.Universe.Base

module Digems.Diff.Algorithm {n : ℕ}(φ : Fam n) where

open import Digems.Universe.Treefix φ
open import Digems.Universe.Subtree φ
open import Digems.Diff.Types φ

-- We will model the whole algorithm assuming we are provided
-- with a 'C'ommon 'S'ubtree 'M'apping between the origin
-- and destination.
--
-- Hence, the moving parts are defined in a pseude Reader monad
-- that has access to such information.
-- 
module WithCSM {ι : Fin n}(src dst : Fix φ ι)(csm : CSM src dst) where

  SharedI : Atom n → Set
  SharedI (K _) = ⊥
  SharedI (I ι) = Σ (Fix φ ι) (λ a → a ⊆Fix src × a ⊆Fix dst)

  -- The first step is to extract the treefixes. We will abstain
  -- from giving names to our holes yet.
  extractTx : ∀{α} → ⟦ α ⟧A (Fix φ) → Tx SharedI α
  extractTx {K κ} atk = opq atk
  extractTx {I ι} ati with csm ati
  ...| nothing  = txStiff ati
  ...| just prf = hole (ati , prf)


diff : ∀{ι} → (x y : Fix φ ι) → Patch (I ι)
diff x y = {!!}

