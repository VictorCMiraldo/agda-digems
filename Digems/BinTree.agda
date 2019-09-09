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
 ⟦ hole x   ⟧ v = Vec-lookup v x
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

 -- I'm lazy to open monads here, so I'll just define apply2
 apply2 : ∀{m n} → Change n → Change m → T ⊥ → Maybe (T ⊥)
 apply2 p q x with apply p x
 ...| nothing = nothing
 ...| just x' = apply q x'

 does-it-merge? : ∀{n m} → Change n → Change m → T ⊥ → Bool
 does-it-merge? p q src with apply2 p q src | apply2 q p src
 ...| just d1 | just d2 with d1 ≟T d2
 ...| yes _ = true
 ...| no  _ = false
 does-it-merge? p q src | _ | _ = false

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

 SameConstr : {A B : Set} → T A → T B → Set
 SameConstr (hole x) (hole x₁)          = ⊥ -- hole is not the same constr; it's more of a meta constr.
 SameConstr (hole x) leaf               = ⊥
 SameConstr (hole x) (fork tb tb₁)      = ⊥
 SameConstr leaf (hole x)               = ⊥
 SameConstr leaf leaf                   = Unit
 SameConstr leaf (fork tb tb₁)          = ⊥
 SameConstr (fork ta ta₁) (hole x)      = ⊥
 SameConstr (fork ta ta₁) leaf          = ⊥
 SameConstr (fork ta ta₁) (fork tb tb₁) = Unit

 data Tᵈ (A B : Set) : Set where
   aunif-res : (ta : T A)(tb : T B)
             → ¬ (SameConstr ta tb)
             → Tᵈ A B

 aunif' : ∀{A B} → T A → T B → T (Tᵈ A B)
 aunif' leaf leaf                   = leaf
 aunif' (fork ta ta₁) (fork tb tb₁) = fork (aunif' ta tb) (aunif' ta₁ tb₁)
 aunif' (hole x) (hole x₁)          = hole (aunif-res (hole x) (hole x₁) id)
 -- Other cases
 aunif' (hole x) leaf               = hole (aunif-res (hole x) leaf id) 
 aunif' (hole x) (fork tb tb₁)      = hole (aunif-res (hole x) leaf id)
 aunif' leaf (hole x)               = hole (aunif-res leaf (hole x) id)
 aunif' leaf (fork tb tb₁)          = hole (aunif-res leaf (fork tb₁ tb₁) id)
 aunif' (fork ta ta₁) (hole x)      = hole (aunif-res leaf (hole x) id)
 aunif' (fork ta ta₁) leaf          = hole (aunif-res (fork ta₁ ta₁) leaf id)

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

 data T-all {A : Set}(P : A → Set) : T A → Set where
   hole : ∀{x} → P x → T-all P (hole x)
   leaf : T-all P leaf
   fork : ∀{l r} → T-all P l → T-all P r → T-all P (fork l r)
 
 Is-copy : ∀{m} → T (Fin m) × T (Fin m) → Set
 Is-copy (hole v , hole u) = v ≡ u
 Is-copy _                 = ⊥

 spined : ∀{n} → Change n → T (Tᵈ (Fin n) (Fin n))
 spined c = aunif' (delCtx c) (insCtx c)

 data _∈T_,_ {m : ℕ} : T ⊥ → T (Fin m) → Vec (Maybe (T ⊥)) m → Set where
   ∈T-hole : ∀{t k} → t ∈T (hole k) , v-singl k t
   ∈T-fork : ∀{l r p p' v v' v''}
           → l ∈T p  , v
           → r ∈T p' , v'
           → v-union v v' ≡ just v''
           → (fork l r) ∈T (fork p p') , v''

 _∈img_ : T ⊥ → ∀{n} → Change n → Set
 t ∈img c = ∃[ v ] (t ∈T (insCtx c) , v)

 AppliesTo : ∀{n} → Change n → T ⊥ → Set
 AppliesTo c t = ∃ (λ res → apply c t ≡ just res)

 𝓐 : ∀{m n} → Tᵈ (Fin m) (Tᵈ (Fin n) (Fin n)) → Set
 𝓐 (aunif-res (hole _) _                     _) = Unit
 𝓐 (aunif-res _ (hole (aunif-res tbi tbd _)) _) = Is-copy (tbi , tbd)
 𝓐 (aunif-res _ _                            _) = ⊥

 lemmaA1 : ∀{m n}(delC : T (Fin m))(d : Change n)
         → T-all 𝓐 (aunif' delC (spined d))
         → ∃[ x ] (x ∈img d × AppliesTo d x)
 lemmaA1 delC d hyp = {!!}
{-

 --------------------
 -- Simple Disjointness
 --------------------

 -- What are the patches p,q such that (apply p ∘ apply q) coincides with
 -- (apply q ∘ apply p) for a given x?
 --
 -- Intuitively, this happens when p and q work on separate parts of
 -- the tree altogether, needing no adaptation. Next we try to prove this thing.

 SpinedChg : ℕ → Set
 SpinedChg n = T (T (Fin n) × T (Fin n))

 spined : ∀{n} → Change n → SpinedChg n
 spined (chg d i) = aunif d i

{-

 -- TD₁ represents a trivial disjointness predicate stating 
 -- two changes do not have overlapping holes AT ALL; it is pretty
 -- simplistic as we can see next.
 data TD₁ {n m : ℕ} : SpinedChg n → SpinedChg m → Set where
   -- First, we have the easy cases recursing on the spine.
   TD-leaf : TD₁ leaf leaf
   TD-fork : ∀{l₁ r₁ l₂ r₂}
           → TD₁ l₁ l₂
           → TD₁ r₁ r₂
           → TD₁ (fork l₁ r₁) (fork l₂ r₂)

   -- Now the interesting bits.
   TD-left  : ∀{id t}
            → Is-copy id
            → TD₁ (hole id) t
   TD-right : ∀{id t}
            → Is-copy id
            → TD₁ t (hole id)

 TrivialDisj₁ : ∀{n m} → Change n → Change m → Set
 TrivialDisj₁ p q = TD₁ (spined p) (spined q)

 -- It does work for simple examples:
 module TD₁-example1 where

   p : Change 3
   p = chg (fork (fork (hole zero) (hole (suc zero)))             (hole (suc (suc zero)))) 
           (fork (fork (fork (hole zero) (hole (suc zero))) leaf) (hole (suc (suc zero))))

   q : Change 2
   q = chg (fork (hole (suc zero)) (fork leaf (hole zero)))
           (fork (hole (suc zero)) (hole zero))

   TD₁-pq : TrivialDisj₁ p q
   TD₁-pq = TD-fork (TD-right refl) (TD-left refl)

   src : T ⊥
   src = fork (fork leaf leaf) (fork leaf leaf)

   merges = does-it-merge? p q src

 -- But breaks as soon as we reuse variables; suggesting we need a better way of handling 
 -- contractions.
 module TD₁-example2 where

   p : Change 3
   p = chg (fork (fork (hole zero) (hole (suc zero)))             (hole (suc (suc zero)))) 
           (fork (fork (fork (hole zero) (hole (suc zero))) leaf) (hole (suc (suc zero))))

   q : Change 1
   q = chg (fork (hole zero) (fork leaf (hole zero)))
           (fork (hole zero) (hole zero))

   TD₁-pq : TrivialDisj₁ p q
   TD₁-pq = TD-fork (TD-right refl) (TD-left refl)

   src : T ⊥
   src = fork (fork leaf leaf) (fork leaf leaf)

   merges = does-it-merge? p q src

-}

 -- Which suggests we should keep track of how and where variables 
 -- are used
 VarInfo₂ : ℕ → Set
 VarInfo₂ = Maybe ∘ SpinedChg 

 VI-Compatible1 : ∀{n}(_ _ : VarInfo₂ n) → Set
 VI-Compatible1 (just x) (just y) = x ≡ y
 VI-Compatible1 (just x) nothing  = Unit
 VI-Compatible1 nothing (just x)  = Unit
 VI-Compatible1 nothing nothing   = Unit

 VI-Compatible : ∀{n m} → Vec (VarInfo₂ n) m → Vec (VarInfo₂ n) m → Set
 VI-Compatible [] [] = Unit
 VI-Compatible (v ∷ vs) (u ∷ us) = VI-Compatible1 v u × VI-Compatible vs us

 VI-∪ : ∀{n m}(v₁ v₂ : Vec (VarInfo₂ n) m) → VI-Compatible v₁ v₂ → Vec (VarInfo₂ n) m
 VI-∪ [] [] _ = []
 VI-∪ (just v  ∷ vs) (just v  ∷ us) (refl , c) = just v  ∷ VI-∪ vs us c
 VI-∪ (nothing ∷ vs) (just u  ∷ us) (_    , c) = just u  ∷ VI-∪ vs us c
 VI-∪ (just v  ∷ vs) (nothing ∷ us) (_    , c) = just v  ∷ VI-∪ vs us c
 VI-∪ (nothing ∷ vs) (nothing ∷ us) (_    , c) = nothing ∷ VI-∪ vs us c

 VI-point : ∀{n m} → Fin m → SpinedChg n → Vec (VarInfo₂ n) m
 VI-point zero    sp = just sp ∷ Vec-replicate nothing
 VI-point (suc x) sp = nothing ∷ VI-point x sp

 data TD₂ {n m : ℕ} : SpinedChg n → SpinedChg m 
                    → Vec (VarInfo₂ m) n 
                    → Vec (VarInfo₂ n) m
                    → Set where
   TD-leaf : ∀{v₁ v₂} → TD₂ leaf leaf v₁ v₂
   TD-fork : ∀{l₁ r₁ l₂ r₂ vl₁ vl₂ vr₁ vr₂}
           → TD₂ l₁ l₂ vl₁ vl₂ 
           → TD₂ r₁ r₂ vr₁ vr₂
           -- For the time being, compatibility is defined as:
           --   If two branches seen the same variable, they seen it
           --   with the same value.
           → (p : VI-Compatible vl₁ vr₁)
           → (q : VI-Compatible vl₂ vr₂)
           → TD₂ (fork l₁ r₁) (fork l₂ r₂) (VI-∪ vl₁ vr₁ p) (VI-∪ vl₂ vr₂ q)

   TD-left  : ∀{x t}
            → TD₂ (hole (hole x , hole x)) t (VI-point x t) (Vec-replicate nothing)
   TD-right : ∀{x t}
            → TD₂ t (hole (hole x , hole x)) (Vec-replicate nothing) (VI-point x t)

 TrivialDisj₂ : ∀{n m} → Change n → Change m → Set
 TrivialDisj₂ {n} {m} p q = Σ (Vec (VarInfo₂ m) n × Vec (VarInfo₂ n) m) 
                              (λ { (v₁ , v₂) → TD₂ (spined p) (spined q) v₁ v₂ })

 module TD₂-example1 where

   p : Change 3
   p = chg (fork (fork (hole zero) (hole (suc zero)))             (hole (suc (suc zero)))) 
           (fork (fork (fork (hole zero) (hole (suc zero))) leaf) (hole (suc (suc zero))))

   q : Change 2
   q = chg (fork (hole zero) (fork leaf (hole zero)))
           (fork (hole zero) (hole zero))


   -- Still not great; we should not be able to write this proof... :/
   TD₂-pq : TrivialDisj₂ p q
   TD₂-pq = (nothing ∷ nothing ∷ just (hole (fork leaf (hole zero) , hole zero)) ∷ [] 
          , just
              (fork (hole (hole zero , fork (hole zero) (hole (suc zero))))
               (hole (hole (suc zero) , leaf))) ∷ nothing ∷ []) 
          , TD-fork TD-right TD-left (unit , unit , unit , unit) (unit , unit , unit)

   src : T ⊥
   src = fork (fork leaf leaf) (fork leaf leaf)

   merges = does-it-merge? p q src


--    TD-right : ∀{id t}
--             → Is-copy id
--             → TD₁ t (hole id)

 --------------------
 -- Disjointness
 --------------------

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

-}
