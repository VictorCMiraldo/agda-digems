open import Digems.Prelude

module Digems.BinTree where

 data T (A : Set) : Set where
   hole : A → T A
   leaf : T A
   fork : T A → T A → T A

 fork-inj : ∀{A}{l₁ l₂ r₁ r₂ : T A}
          → fork l₁ r₁ ≡ fork l₂ r₂
          → l₁ ≡ l₂ × r₁ ≡ r₂
 fork-inj refl = refl , refl

 _≟T_ : (x y : T ⊥) → Dec (x ≡ y)
 _        ≟T (hole ())
 hole ()  ≟T leaf
 hole ()  ≟T fork l r
 leaf     ≟T leaf     = yes refl
 leaf     ≟T fork l r = no (λ ())
 fork l r ≟T leaf     = no (λ ())
 fork l r ≟T fork l' r' 
   with l ≟T l' | r ≟T r' 
 ...| yes refl | yes refl = yes refl
 ...| no  abs  | yes refl = no (abs ∘ proj₁ ∘ fork-inj)
 ...| yes refl | no  abs  = no (abs ∘ proj₂ ∘ fork-inj)
 ...| no  abs  | no  _    = no (abs ∘ proj₁ ∘ fork-inj)

 v-singl : ∀{n A} → Fin n → A → Vec {lz} (Maybe A) n
 v-singl zero    a = just a ∷ Vec-replicate nothing
 v-singl (suc f) a = nothing ∷ v-singl f a

 v-union : ∀{n} 
         → Vec {lz} (Maybe (T ⊥)) n 
         → Vec {lz} (Maybe (T ⊥)) n 
         → Maybe (Vec {lz} (Maybe (T ⊥)) n)
 v-union []       []       = just []
 v-union (nothing ∷ ms) (nothing ∷ ns) = Maybe-map (nothing ∷_) (v-union ms ns)
 v-union (just m  ∷ ms) (nothing ∷ ns) = Maybe-map (just m  ∷_) (v-union ms ns)
 v-union (nothing ∷ ms) (just n  ∷ ns) = Maybe-map (just n  ∷_) (v-union ms ns)
 v-union (just m  ∷ ms) (just n  ∷ ns) 
   with m ≟T n
 ...| yes _ = Maybe-map (just m ∷_) (v-union ms ns)
 ...| no  _ = nothing

 match : ∀{n} → T (Fin n) → T ⊥ → Maybe (Vec (Maybe (T ⊥)) n)
 match (hole x)   v = just (v-singl x v)
 match leaf       v = just (Vec-replicate nothing)
 match (fork l r) (fork vl vr) 
   with match l vl | match r vr
 ...| just mr | just ml = v-union mr ml
 ...| _       | _       = nothing
 match (fork l r) _ = nothing

 ⟦_⟧ : ∀{n} → T (Fin n) → Vec (Maybe (T ⊥)) n → Maybe (T ⊥)
 ⟦ hole x   ⟧ v = Vec-lookup x v
 ⟦ leaf     ⟧ v = just leaf
 ⟦ fork l r ⟧ v 
   with ⟦ l ⟧ v | ⟦ r ⟧ v 
 ...| just l' | just r' = just (fork l' r')
 ...| _       | _       = nothing

 record Change (n : ℕ) : Set where
   constructor chg
   field
     delCtx : T (Fin n)
     insCtx : T (Fin n)
 open Change

 apply : ∀{n} → Change n → T ⊥ → Maybe (T ⊥)
 apply (chg d i) x with match d x
 ...| nothing = nothing
 ...| just v  = ⟦ i ⟧ v

 -----------------------
 -- Examples
 ----------------------

 chg-swap : Change 2
 chg-swap = chg (fork (hole zero) (hole (suc zero)))
                (fork (hole (suc zero)) (hole zero))

 chg-contract : Change 1
 chg-contract = chg (fork (hole zero) (hole zero)) (hole zero)

 -----------------
 -- Usefull functions
 -----------------

 μ : ∀{A} → T (T A) → T A
 μ leaf       = leaf
 μ (hole t)   = t
 μ (fork l r) = fork (μ l) (μ r)

 aunif : ∀{A B} → T A → T B → T (T A × T B)
 aunif (fork l r) (fork l' r') = fork (aunif l l') (aunif r r')
 aunif leaf       leaf         = leaf
 aunif x          y            = hole (x , y)
 -- aunif (hole x)   (hole y)     = hole (hole x , hole y)
 -- aunif (hole x)   leaf         = hole (hole x , leaf)
 -- aunif (hole x)   (fork l r)   = hole (hole x , fork l r)
 -- aunif leaf       (hole y)     = hole (leaf , hole y)
 -- aunif leaf       (fork l r)   = hole (leaf , fork l r)
 -- aunif (fork l r) (hole y)     = hole (fork l r , hole y)
 -- aunif (fork l r) leaf         = hole (fork l r , leaf)

 --------------------
 -- Disjointness
 --------------------

 data T-all {A : Set}(P : A → Set) : T A → Set where
   hole : ∀{x} → P x → T-all P (hole x)
   leaf : T-all P leaf
   fork : ∀{l r} → T-all P l → T-all P r → T-all P (fork l r)

 T2 : Set → Set
 T2 A = T (T A × T A)

 A : ∀{m n} → T (Fin n) → T2 (Fin m) → Set
 A delp q = T-all ok (aunif delp q)
   where
     ok : ∀{n m} → T (Fin n) × T2 (Fin m) → Set
     ok (hole _ , _)                      = Unit
     ok (_      , hole (hole x , hole y)) = x ≡ y
     ok _                                 = ⊥
     

 --------------------
 -- Merging
 --------------------

 -- This will be pretty difficult; We might need a more expressive type of trees.
 -- Something that counts occurences could be interesting:
 --  
 -- data T (n : ℕ) : Vec ℕ n → Set where
 --   hole : (v : Fin n) → T (set 1 v) n
 --   leaf : T n (const 0)
 --   fork : T n v₁ → T n v₂ → T n (sum-pointwise v₁ v₂)
