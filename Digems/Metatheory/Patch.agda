open import Digems.Prelude
open import Digems.Universe.Base using (Fam)

module Digems.Metatheory.Patch {n : ℕ}(φ : Fam n) where

 open import Digems.Universe φ
 
 module WithArity (arity : ℕ)(typeOfVar : Fin arity → Atom n) where

  open import Digems.Universe.Treefix φ public

  TxVar : Atom n → Set
  TxVar α = Σ (Fin arity) (λ f → α ≡ typeOfVar f)

  Tx : Atom n → Set
  Tx = UTx TxVar

  TxSubst : Set
  TxSubst = (v : Fin arity) → Tx (typeOfVar v)

{-
  TermSubst : Set
  TermSubst = (v : Fin arity) → Maybe (⟦ typeOfVar v ⟧A)

  ∅ : TermSubst
  ∅ _ = nothing

  _↦_ : (v : Fin arity) → ⟦ typeOfVar v ⟧A
      → TermSubst
  (v ↦ el) v' with v ≟F v'
  ...| yes refl = just el
  ...| no  _    = nothing
-}

  open import Data.Vec.All 
    using ([] ; _∷_)
    renaming (All to Vec-All; lookup to Vec-All-lookup)

  idx-table : ∀{n} → Vec (Fin n) n
  idx-table {zero}  = []
  idx-table {suc n} = zero ∷ Vec-map suc idx-table

  postulate
    vec-lookup-map : ∀{n}{A B : Set}(vs : Vec A n)(f : A → B)
                   → (i : Fin n)
                   → Vec-lookup (Vec-map f vs) i ≡ f (Vec-lookup vs i)
    -- vec-lookup-map = {!!}

  idx-table-lkup : ∀{n}(i : Fin n) → Vec-lookup idx-table i ≡ i
  idx-table-lkup zero    = refl
  idx-table-lkup (suc i) = trans (vec-lookup-map idx-table suc i) 
                                 (cong suc (idx-table-lkup i))

  idx-table-arity : Vec (Fin arity) arity
  idx-table-arity = idx-table

  TermSubst : Set
  TermSubst = Vec-All (λ vᵢ → Maybe ⟦ typeOfVar vᵢ ⟧A) 
                      idx-table-arity

  Vec-All-replicate : ∀{a b n}{A : Set a}
                    → {P : A → Set b}
                    → (∀ {a} → P a) 
                    → (vs : Vec A n) 
                    → Vec-All P vs
  Vec-All-replicate f [] = []
  Vec-All-replicate f (x ∷ vs) = f {x} ∷ Vec-All-replicate f vs

  Vec-All-set : ∀{a b n}{A : Set a}
                 → {P : A → Set b}
                 → (idx : Fin n)
                 → {vs : Vec A n}
                 → P (Vec-lookup vs idx)
                 → Vec-All P vs
                 → Vec-All P vs
  Vec-All-set ()      x [] 
  Vec-All-set zero    x (_  ∷ xs) = x ∷ xs
  Vec-All-set (suc n) x (x' ∷ xs) = x' ∷ Vec-All-set n x xs

  t∅ : TermSubst
  t∅ = Vec-All-replicate nothing idx-table-arity

  _↦_ : (v : Fin arity) → ⟦ typeOfVar v ⟧A → TermSubst
  vᵢ ↦ tᵢ = Vec-All-set vᵢ (subst (Maybe ∘ ⟦_⟧A ∘ typeOfVar) 
                                (sym (idx-table-lkup vᵢ)) (just tᵢ)) 
                       t∅

  t-lkup : (v : Fin arity) → TermSubst → Maybe ⟦ typeOfVar v ⟧A
  t-lkup v σ rewrite sym (idx-table-lkup v) 
    =  Vec-All-lookup v σ 

  Vec-All-combine : ∀{a b n}{A : Set a}
                  → {P Q R : A → Set b}
                  → {vs : Vec A n}
                  → (∀{α} → P α → Q α → Maybe (R α))
                  → Vec-All P vs
                  → Vec-All Q vs
                  → Maybe (Vec-All R vs)
  Vec-All-combine f [] [] = just []
  Vec-All-combine f (px ∷ ps) (qx ∷ qs) with f px qx
  ...| nothing = nothing
  ...| just rx = Maybe-map (rx ∷_) (Vec-All-combine f ps qs)


  ⟦⟧A-combine : ∀{α} → Maybe ⟦ α ⟧A → Maybe ⟦ α ⟧A → Maybe (Maybe ⟦ α ⟧A)
  ⟦⟧A-combine {a} (just x) (just x₁) with _≟A_ {a} x x₁
  ...| yes _ = just (just x)
  ...| no  _ = nothing
  ⟦⟧A-combine (just x) nothing = just (just x)
  ⟦⟧A-combine nothing (just x) = just (just x)
  ⟦⟧A-combine nothing nothing = nothing

  t-combine : List (Maybe TermSubst) → Maybe TermSubst
  t-combine [] = just t∅
  t-combine (nothing ∷ _) = nothing
  t-combine (just x  ∷ xs) with t-combine xs
  ...| nothing  = nothing
  ...| just xs' = Vec-All-combine (λ {vᵢ} → ⟦⟧A-combine {typeOfVar vᵢ}) x xs'

 {- 
  insert : (v : Fin arity) → ⟦ typeOfVar v ⟧A
         → TermSubst → Maybe TermSubst
  insert v el σ with σ v
  ...| nothing = just ((v ↦ el) σ)
  ...| just el' with _≟A_ {typeOfVar v} el el'
  ...| yes _ = just σ
  ...| no  _ = nothing
-}

  -- Which variables appear in a 'Tx'?

  v∅ : Vec Bool arity
  v∅ = Vec-replicate false

  set-bit : ∀{α} → TxVar α → Vec Bool arity
  set-bit (idx , _) = Vec-updateAt idx (const true) v∅

  and* : List (Vec Bool arity) → Vec Bool arity
  and* []       = v∅
  and* (x ∷ xs) = Vec-zipWith _∧_ x (and* xs)

  txVars : ∀{α} → Tx α → Vec Bool arity
  txVars = txFoldMon set-bit (const v∅) and*

  record Patch (α : Atom n) : Set where
    constructor patch
    field
      del : Tx α
      ins : Tx α
      wf  : txVars del ≡ txVars ins
