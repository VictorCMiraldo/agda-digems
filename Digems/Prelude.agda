module Digems.Prelude where

-- * Levels

open import Level
  using ()
  renaming (zero to lz; suc to ls; _⊔_ to _⊔ₗ_)
  public

-- * Homogeneous Equality and Decidability

open import Relation.Nullary
  public

open import Relation.Binary.PropositionalEquality
  public

-- * Polynomial Functors

open import Data.Unit.NonEta
  public

open import Data.Empty
  public

open import Data.Product
  renaming (map to ×-map; swap to ×-swap)
  public

open import Data.Sum
  renaming (map to ⊎-map; swap to ⊎-swap)
  public

-- ** Handy aliases

infixr 3 _><_ _-|-_
_><_ : ∀ {a b p q}
         {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
     → (f : A → B) → (∀ {x} → P x → Q (f x)) 
     → Σ A P → Σ B Q
_><_ = ×-map

_-|-_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
      → (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
_-|-_ = ⊎-map

-- * Base Types and Handy stuff

open import Function 
  hiding (_⟨_⟩_)
  public

open import Data.Maybe 
  using (Maybe ; nothing ; just ; maybe)
  renaming (map to Maybe-map)
  public

open import Data.Bool
  using (Bool ; true ; false) 
  renaming (_≟_ to _≟B_)
  public

open import Data.Fin 
  using (Fin ; suc ; zero; inject₁)
  public

open import Data.Fin.Properties 
  using ()
  renaming (_≟_ to _≟F_)
  public

open import Data.Nat 
  renaming (_≟_ to _≟N_)
  hiding (_⊓_)
  public

open import Data.List
  using (List ; _∷_ ; [] ; length ; _++_)
  renaming (map to List-map ; zip to List-zip)
  public

open import Data.List.All
  using (All ; _∷_ ; []) 
  renaming (map to All-map)
  public

All-∷-inj 
  : ∀{a}{A : Set a}{P : A → Set}{x : A}{xs : List A}
  → {px py : P x}{pxs pys : All P xs}
  → _≡_ {A = All P (x ∷ xs)} (px ∷ pxs) (py ∷ pys) → px ≡ py × pxs ≡ pys
All-∷-inj refl = refl , refl

open import Data.List.Any
  hiding (map)
  public

Any-there-inj
  : ∀{a}{A : Set a}{P : A → Set}{x : A}{xs : List A}
  → {px py : Any P xs}
  → _≡_ {A = Any P (x ∷ xs)} (there px) (there py)
  → px ≡ py
Any-there-inj refl = refl

open import Data.Vec
  using (Vec ; _∷_; [])
  renaming (map to Vec-map ; lookup to Vec-lookup)
  public

open import Data.String
  using (String ; primStringEquality)
  renaming (_++_ to strcat)
  public

_≟Str_ : (x y : String) → Dec (x ≡ y)
x ≟Str y with primStringEquality x y
...| true  = yes primTrustMe
  where open import Agda.Builtin.TrustMe
...| false = no (const magic)
  where postulate magic : ⊥


