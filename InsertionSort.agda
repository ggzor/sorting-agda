open import Sorting

insert : (x : ℕ) → (l : List ℕ) → List ℕ
insert x [] = x ∷ []
insert x (y ∷ l) with ≤-total x y
... | inj₁ x≤y = x ∷ y ∷ l
... | inj₂ y≤x = y ∷ insert x l

insertion-sort : List ℕ → List ℕ
insertion-sort [] = []
insertion-sort (x ∷ l) = insert x (insertion-sort l)

≤*-insert : (x y : ℕ) (l : List ℕ) → x ≤ y → x ≤* l → x ≤* insert y l
≤*-insert x y [] x≤y x≤*l = x≤y , tt
≤*-insert x y (z ∷ l) x≤y (x≤z , z≤*l) with ≤-total y z
... | inj₁ y≤z = x≤y , x≤z , z≤*l
... | inj₂ z≤y = x≤z , (≤*-insert x y l x≤y z≤*l)

insert-sorting : (x : ℕ) → (l : List ℕ) → sorted l → sorted (insert x l)
insert-sorting x [] sl = tt , tt
insert-sorting x (y ∷ l) (y≤*l , sl) with ≤-total x y
... | inj₁ x≤y = (x≤y , ≤*-trans x≤y y≤*l) , y≤*l , sl
... | inj₂ y≤x = ≤*-insert y x l y≤x y≤*l , insert-sorting x l sl

insertion-sort-sorts : ∀ (l : List ℕ) → sorted (insertion-sort l)
insertion-sort-sorts [] = tt
insertion-sort-sorts (x ∷ l) = insert-sorting x (insertion-sort l) (insertion-sort-sorts l)

insert-~ : (x : ℕ) (l : List ℕ) → (x ∷ l) ~ (insert x l)
insert-~ x [] = ~-drop x ~-nil
insert-~ x (y ∷ l) with ≤-total x y
... | inj₁ x≤y = ~-refl
... | inj₂ y≤x = ~-trans (~-swap x y l) (~-drop y (insert-~ x l))

~-insert : (x : ℕ) {l l' : List ℕ} → l ~ l' → insert x l ~ insert x l'
~-insert x {l} {l'} l~l' =
  let a = ~-sym (insert-~ x l)
      b = insert-~ x l'
      c = ~-drop x l~l'
    in ~-trans (~-trans a c) b

insertion-sort-~ : (l : List ℕ) → l ~ (insertion-sort l)
insertion-sort-~ [] = ~-nil
insertion-sort-~ (x ∷ l) = ~-trans (~-drop x (insertion-sort-~ l)) (insert-~ x (insertion-sort l))

insertion-sort-correct : (l : List ℕ) → sorted (insertion-sort l) × l ~ insertion-sort l
insertion-sort-correct l = insertion-sort-sorts l , insertion-sort-~ l

