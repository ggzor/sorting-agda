open import Sorting

open import Data.Sum using (inj₁; inj₂)
open import Data.Nat.Properties using (≤-total)

insert : (x : ℕ) → (l : List ℕ) → List ℕ
insert x [] = x ∷ []
insert x (y ∷ l) with ≤-total x y
... | inj₁ x≤y = x ∷ y ∷ l
... | inj₂ y≤x = y ∷ insert x l

insertion-sort : List ℕ → List ℕ
insertion-sort [] = []
insertion-sort (x ∷ l) = insert x (insertion-sort l)

≤*-insert : ∀ (x y : ℕ) (l : List ℕ) → x ≤ y → x ≤* l → x ≤* insert y l
≤*-insert x y [] x≤y x≤*l = x≤y , tt
≤*-insert x y (z ∷ l) x≤y (x≤z , z≤*l) with ≤-total y z
... | inj₁ y≤z = x≤y , x≤z , z≤*l
... | inj₂ z≤y = x≤z , (≤*-insert x y l x≤y z≤*l)

insert-preserves-sorted :  ∀ (x : ℕ) (l : List ℕ)
                        →  sorted l
                        →  sorted (insert x l)
insert-preserves-sorted x [] sl = tt , tt
insert-preserves-sorted x (y ∷ l) (y≤*l , sl) with ≤-total x y
... | inj₁ x≤y = (x≤y , ≤*-trans x≤y y≤*l) , y≤*l , sl
... | inj₂ y≤x =
        ≤*-insert y x l y≤x y≤*l , insert-preserves-sorted x l sl

insertion-sort-sorts : ∀ (l : List ℕ) → sorted (insertion-sort l)
insertion-sort-sorts [] = tt
insertion-sort-sorts (x ∷ l) =
  let  h-ind = insertion-sort-sorts l
   in  insert-preserves-sorted x (insertion-sort l) h-ind
                            
insert-~ : (x : ℕ) (l : List ℕ) → (x ∷ l) ~ (insert x l)
insert-~ x [] = ~-drop x ~-nil
insert-~ x (y ∷ l) with ≤-total x y
... | inj₁ x≤y = ~-refl
... | inj₂ y≤x = ~-trans (~-swap x y l) (~-drop y (insert-~ x l))

~-insert : (x : ℕ) {l l' : List ℕ} → l ~ l' → insert x l ~ insert x l'
~-insert x {l} {l'} l~l' =
  let p1 = ~-sym (insert-~ x l)
      p2 = insert-~ x l'
      mid = ~-drop x l~l'
   in ~-trans p1 (~-trans mid p2)

insertion-sort-~ : (l : List ℕ) → l ~ (insertion-sort l)
insertion-sort-~ [] = ~-nil
insertion-sort-~ (x ∷ l) =
  let h-ind = insertion-sort-~ l
      p1 = insert-~ x l
      p2 = ~-insert x h-ind
   in ~-trans p1 p2

insertion-sort-correct : Correct-Sorting-Algorithm insertion-sort
insertion-sort-correct l =
  insertion-sort-sorts l , insertion-sort-~ l

