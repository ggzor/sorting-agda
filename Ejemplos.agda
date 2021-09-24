module Ejemplos where

open import Sorting

-- doc:start-here

-- Ejemplos de naturales y listas
n1 : ℕ
n1 = suc (suc zero)

n1' : ℕ
n1' = 2

list1 : List ℕ
list1 = 1 ∷ 2 ∷ 3 ∷ []

-- Ejemplos de la relación menor o igual
open import Data.Nat using (z≤n; s≤s)

le1 : 0 ≤ 1
le1 = z≤n

le2 : 1 ≤ 2
le2 = s≤s z≤n

-- Ejemplos acotación
ac1 : 1 ≤* (2 ∷ 3 ∷ [])
ac1 = s≤s z≤n , s≤s z≤n , tt

-- El tipo de ac1 normalizado
ac1' : 1 ≤ 2 × 1 ≤ 3 × ⊤
ac1' = s≤s z≤n , s≤s z≤n , tt

-- No sort
no-sort : List ℕ → List ℕ
no-sort l = []

no-sort-sorts : ∀ (l : List ℕ) → sorted (no-sort l)
no-sort-sorts l = tt

-- Ejemplos de permutaciones
perm1 : (1 ∷ 2 ∷ 3 ∷ []) ~ (3 ∷ 1 ∷ 2 ∷ [])
perm1 =
  let p1 = ~-swap 1 3 (2 ∷ [])
      p2 = ~-drop 1 (~-swap 2 3 [])
   in ~-trans p2 p1

