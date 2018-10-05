open import Digems.Prelude
open import Digems.Prelude.Any2
open import Digems.Universe.Family

module Digems.Universe.Location {n : ℕ}(φ : Fam n) where

open import Digems.Universe φ

-- Defines a location inside a value of type α
{-
mutual
  data LocNP : Prod n → Set where
    here  : ∀{α π} → Loc α   → LocNP (α ∷ π)
    there : ∀{α π} → LocNP π → LocNP (α ∷ π)
-}
open import Data.Maybe using (monadPlus)
open RawMonadPlus {lz} monadPlus

-- An inhebitant of 'Loc α β' gives a location for some
-- tree of type β inside a tree of type 'α'
data Loc : Atom n → Atom n → Set where
  here : ∀{α} → Loc α α
  peel : ∀{α ν}(c : Constr ν)
       → Any (flip Loc α) (typeOf ν c)
       → Loc (I ν) α

Any-lift : {A : Set}{l : List A}{P : A → Set}
         → (∀{a} → P a → P a → Set)
         → Set
         → (x y : Any P l)
         → Set
Any-lift R U (here p₁)  (here p₂)  = R p₁ p₂
Any-lift R U (here _)   (there _)  = U
Any-lift R U (there _)  (here _)   = U
Any-lift R U (there p₁) (there p₂) = Any-lift R U p₁ p₂

-- Relates two disjoint, but compatible locations
{-# TERMINATING #-}
Loc-disj : ∀{α β} → (l₁ l₂ : Loc α β) → Set
Loc-disj here here       = ⊥
Loc-disj here (peel _ _) = ⊥
Loc-disj (peel _ _) here = ⊥
Loc-disj (peel c₁ l₁) (peel c₂ l₂)
  = Σ (c₁ ≡ c₂) (λ { refl → Any-lift Loc-disj Unit l₁ l₂ })

{-# TERMINATING #-}
Loc-match : ∀{α β} → Loc α β → ⟦ α ⟧A → Maybe ⟦ β ⟧A
Loc-match here a = just a
Loc-match (peel c x) ⟨ a ⟩ 
  = match c a >>= λ xs 
  → let (_ , l' , a') = AnyAll-select x xs
     in Loc-match l' a'



{-
{-# TERMINATING #-}
Loc-inj : ∀{α β} → ⟦ β ⟧A → Loc α β → ⟦ α ⟧A → Maybe ⟦ α ⟧A
Loc-inj b here _ = just b
Loc-inj b (peel c x) ⟨ a ⟩ 
  = match c a >>= λ xs 
  → {!!}
-}



{-
-- We now relate the locations that are valid within a value
data _Loc∈_ : {α : Atom n} → Loc α → ⟦ α ⟧A → Set where
  here  : ∀{α}{a : ⟦ α ⟧A} → _Loc∈_ {α} here a
  there : ∀{ν}(c : Constr ν)
        → {p : ⟦ typeOf ν c ⟧P}
        → (l : Any Loc (typeOf ν c))
        → let (_ , loc , at) = AnyAll-select l p
           in loc Loc∈ at
        → (peel {ν} c l) Loc∈ ⟨ inj c p ⟩

Loc∈? : {α : Atom n}(l : Loc α)(a : ⟦ α ⟧A)
      → Dec (l Loc∈ a)
Loc∈? here a            = yes here
Loc∈? (peel c x) ⟨ a ⟩ with sop a
...| tag cₐ pₐ with c ≟F cₐ
...| no abs   = no (λ { (there {ν} c {p} l hip) → {!!} })
...| yes refl = {!!}

-}
