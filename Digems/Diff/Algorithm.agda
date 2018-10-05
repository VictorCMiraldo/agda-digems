open import Digems.Prelude
open import Digems.Universe.Family

open import Data.AVL.IndexedMap

module Digems.Diff.Algorithm {n : ℕ}(φ : Fam n) where

open import Digems.Universe φ
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

  -- This is a proof that an tree is a common subtree of
  -- both the source and destination of our patch.
  SharedI : Atom n → Set
  SharedI (K _) = ⊥
  SharedI (I ι) = Σ (Fix φ ι) (λ a → a ⊆Fix src × a ⊆Fix dst)

  _≟SI_ : ∀{α₁ α₂}(s₁ : SharedI α₁)(s₂ : SharedI α₂)
        → Dec (Σ (α₁ ≡ α₂) (λ { refl → s₁ ≡ s₂ }))
  _≟SI_ {K _ } {K _ } _ ()
  _≟SI_ {I _ } {K _ } _ ()
  _≟SI_ {K _ } {I _ } () _
  _≟SI_ {I ι₁} {I ι₂} (a₁ , s₁) (a₂ , s₂) with ι₁ ≟F ι₂
  ...| no  ι₁≢ι₂ = no ((λ { refl → ι₁≢ι₂ refl}) ∘ proj₁)
  ...| yes refl  = {!!}

  -- The first step is to extract the treefixes. We will abstain
  -- from giving names to our holes yet.
  {-# TERMINATING #-}
  extractTx : ∀{α} → ⟦ α ⟧A → Tx SharedI α
  extractTx {K κ} atk = opq atk
  extractTx {I ι} ⟨ ati ⟩ with csm ⟨ ati ⟩
  ...| just prf = hole ( ⟨ ati ⟩ , prf)
  ...| nothing with sop ati
  ...| tag c p = peel c (All-map extractTx p)


diff : ∀{ι} → (x y : Fix φ ι) → Patch (I ι)
diff {ι} x y 
  = let dx₀ = extractTx {I ι} x
        dy₀ = extractTx {I ι} y
        vx  = txHoles dx₀
        vy  = txHoles dy₀
     in {!!}
  where
    open WithCSM x y {!!}

