module Sorting where

open import Data.Nat using (ℕ; suc; zero) public
open import Data.List using (List; _∷_; []) public

open import Data.Nat using (_≤_) public

open import Data.Unit using (⊤; tt) public
open import Data.Product using (_×_; _,_) public

-- Less Than All Relation
_≤*_ : (x : ℕ) → (l : List ℕ) → Set
x ≤* [] = ⊤
x ≤* (y ∷ l) = (x ≤ y) × (x ≤* l)

sorted : (l : List ℕ) → Set
sorted [] = ⊤
sorted (x ∷ l) = x ≤* l × sorted l

-- Permutations
data _~_ {A : Set} : List A → List A → Set where
  ~-nil    :                              [] ~ []
  ~-drop   : (x : A) { l l' : List A}  →  l ~ l' → (x ∷ l) ~ (x ∷ l')
  ~-swap   : (x y : A) (l : List A)    →  (x ∷ y ∷ l) ~ (y ∷ x ∷ l)
  ~-trans  : {l l' l'' : List A}       →  l ~ l' → l' ~ l'' → l ~ l''

Correct-Sorting-Algorithm : (f : List ℕ → List ℕ) → Set
Correct-Sorting-Algorithm f = ∀ (l : List ℕ) → sorted (f l) × l ~ f l

-- Properties of ≤*
open import Data.Nat.Properties using (≤-trans)

≤*-trans : {x y : ℕ} {l : List ℕ} → x ≤ y → y ≤* l → x ≤* l
≤*-trans {l = []} x≤y y≤*l = tt
≤*-trans {l = z ∷ l} x≤y (x≤z , y≤*l) =
  ≤-trans x≤y x≤z , ≤*-trans x≤y y≤*l

-- Properties of ~
~-refl : {A : Set} {l : List A} → l ~ l
~-refl {l = []}     = ~-nil
~-refl {l = x ∷ l}  = ~-drop x ~-refl

~-sym : {A : Set} {l l' : List A} → l ~ l' → l' ~ l
~-sym ~-nil                  = ~-nil
~-sym (~-drop x l~l')        = ~-drop x (~-sym l~l')
~-sym (~-swap x y l)         = ~-swap y x l
~-sym (~-trans l~l'' l''~l)  = ~-trans (~-sym l''~l) (~-sym l~l'')

