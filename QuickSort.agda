open import Sorting

open import Data.Sum using (inj₁; inj₂)
open import Data.Nat.Properties using (≤-total)

divide-list : ℕ → List ℕ → List ℕ × List ℕ
divide-list x [] = [] , []
divide-list x (y ∷ l) with divide-list x l | ≤-total y x
... | l , g | inj₁ y≤x = (y ∷ l) , g
... | l , g | inj₂ x≤y = l , (y ∷ g)

open import Data.List using (length; _++_)

-- {-# TERMINATING #-}
-- quicksort' : List ℕ → List ℕ
-- quicksort' [] = []
-- quicksort' (x ∷ l) =
--   let le , gr = divide-list x l
--   in quicksort' le ++ (x ∷ []) ++ quicksort' gr

open import Data.Nat using (z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-step)

divide-list-less : (x : ℕ) → (l : List ℕ) → let le , gr = divide-list x l
                                             in length le ≤ length l × length gr ≤ length l
divide-list-less _ [] = z≤n , z≤n
divide-list-less x (y ∷ l) with divide-list-less x l | ≤-total y x
... | p1 , p2 | inj₁ y≤x = s≤s p1 , ≤-step p2
... | p1 , p2 | inj₂ x≤y = ≤-step p1 , (s≤s p2)

quicksort-fuel : (l : List ℕ) → (n : ℕ) → (length l ≤ n) → List ℕ
quicksort-fuel [] n p = []
quicksort-fuel (x ∷ l) (suc n) (s≤s p) with divide-list-less x l
... | le≤l , gr≤l = let le , gr = divide-list x l
                    in     (quicksort-fuel le n (≤-trans le≤l p))
                        ++ (x ∷ [])
                        ++ (quicksort-fuel gr n (≤-trans gr≤l p))

quicksort : List ℕ → List ℕ
quicksort l = quicksort-fuel l (length l) ≤-refl

_≥*_ : ℕ → List ℕ → Set
x ≥* [] = ⊤
x ≥* (y ∷ ys) = y ≤ x × x ≥* ys

≤*-++ : {x : ℕ} {xs ys : List ℕ} → x ≤* xs → x ≤* ys → x ≤* (xs ++ ys)
≤*-++ {xs = []} x≤*xs x≤*ys = x≤*ys
≤*-++ {xs = z ∷ xs} (x≤z , x≤*xs) x≤*ys = x≤z , ≤*-++ x≤*xs x≤*ys

≥*-++ : {x : ℕ} {xs ys : List ℕ} → x ≥* xs → x ≥* ys → x ≥* (xs ++ ys)
≥*-++ {xs = []} x≤*xs x≤*ys = x≤*ys
≥*-++ {xs = z ∷ xs} (z≤x , x≥*xs) x≤*ys = z≤x , ≥*-++ x≥*xs x≤*ys

divide-list-compare : (x : ℕ) → (l : List ℕ) → let le , gr = divide-list x l
                                                in x ≥* le × x ≤* gr
divide-list-compare x [] = tt , tt
divide-list-compare x (y ∷ l) with ≤-total y x
... | inj₁ y≤x =
  let x≥*le , x≤*gr = divide-list-compare x l
   in (y≤x , x≥*le) , x≤*gr
... | inj₂ x≤y =
  let x≥*le , x≤*gr = divide-list-compare x l
   in x≥*le , (x≤y , x≤*gr)

divide-list-preserves-≤* : (y : ℕ) {x : ℕ} {l : List ℕ}
                          → x ≤* l
                          → let le , gr = divide-list y l
                             in x ≤* le × x ≤* gr
divide-list-preserves-≤* y {l = []}     x≤*l = tt , tt
divide-list-preserves-≤* y {l = z ∷ l} (x≤z , x≤*l) with ≤-total z y
... | inj₁ z≤y =
  let x≤*le , x≤*gr = divide-list-preserves-≤* y x≤*l
   in (x≤z , x≤*le) , x≤*gr
... | inj₂ y≤z =
  let x≤*le , x≤*gr = divide-list-preserves-≤* y x≤*l
   in x≤*le , (x≤z , x≤*gr)

divide-list-preserves-≥* : (y : ℕ) {x : ℕ} {l : List ℕ}
                          → x ≥* l
                          → let le , gr = divide-list y l
                             in x ≥* le × x ≥* gr
divide-list-preserves-≥* y {l = []}    x≥*l = tt , tt
divide-list-preserves-≥* y {l = z ∷ l} (z≤x , x≥*l) with ≤-total z y
... | inj₁ z≤y =
   let x≥*le , x≥*gr = divide-list-preserves-≥* y x≥*l
    in (z≤x , x≥*le) , x≥*gr
... | inj₂ y≤z =
   let x≥*le , x≥*gr = divide-list-preserves-≥* y x≥*l
    in x≥*le , (z≤x , x≥*gr)

quicksort-preserves-≤* : {x : ℕ} {l : List ℕ}
                       → {n : ℕ} {p : length l ≤ n}
                       → x ≤* l
                       → x ≤* quicksort-fuel l n p
quicksort-preserves-≤* {x} {[]} {n} {p} x≤*l = tt
quicksort-preserves-≤* {x} {y ∷ l} {suc n} {s≤s p} (x≤y , x≤*l) with divide-list-less y l
... | lenle , lengr =
  let x≤*le , x≤*gr = divide-list-preserves-≤* y x≤*l
      x≤*qsort-le = quicksort-preserves-≤* x≤*le
      x≤*qsort-gr = quicksort-preserves-≤* x≤*gr
   in ≤*-++ x≤*qsort-le (x≤y , x≤*qsort-gr)

quicksort-preserves-≥* : {x : ℕ} {l : List ℕ}
                       → {n : ℕ} {p : length l ≤ n}
                       → x ≥* l
                       → x ≥* quicksort-fuel l n p
quicksort-preserves-≥* {x} {[]} {n} {p} x≥*l = tt
quicksort-preserves-≥* {x} {y ∷ l} {suc n} {s≤s p} (y≤x , x≥*l) with divide-list-less y l
... | lenle , lengr =
  let x≥*le , x≥*gr = divide-list-preserves-≥* y x≥*l
      x≥*qsort-le = quicksort-preserves-≥* x≥*le
      x≥*qsort-gr = quicksort-preserves-≥* x≥*gr
   in ≥*-++ x≥*qsort-le (y≤x , x≥*qsort-gr)

join-sorted : {x : ℕ} {l m : List ℕ}
            → sorted l → sorted m
            → x ≥* l → x ≤* m
            → sorted (l ++ (x ∷ []) ++ m)
join-sorted {l = []}    sl sm x≥*l x≤*m = x≤*m , sm
join-sorted {l = y ∷ l} (y≤*l , sl) sm (y≤x , x≥*l) x≤*m =
  ≤*-++ y≤*l (y≤x , (≤*-trans y≤x x≤*m)) , join-sorted sl sm x≥*l x≤*m

quicksort-fuel-sorts : (l : List ℕ)
                → {n : ℕ} {p : length l ≤ n}
                → sorted (quicksort-fuel l n p)
quicksort-fuel-sorts [] = tt
quicksort-fuel-sorts (x ∷ l) {suc n} {s≤s p} with divide-list-less x l
... | lenle , lengr =
  let le , gr = divide-list x l
      le-sorted = quicksort-fuel-sorts le
      gr-sorted = quicksort-fuel-sorts gr
      x≥*le , x≤*gr = divide-list-compare x l
   in join-sorted le-sorted gr-sorted
                  (quicksort-preserves-≥* x≥*le)
                  (quicksort-preserves-≤* x≤*gr)

quicksort-sorts : (l : List ℕ) → sorted (quicksort l)
quicksort-sorts l = quicksort-fuel-sorts l

open import Data.Product using (Σ-syntax)

~-uncons : {l xs : List ℕ} {x : ℕ}
         → l ~ (x ∷ xs)
         → Σ[ l' ∈ List ℕ ] l' ~ xs × l ~ (x ∷ l')
~-uncons {xs = []}     l~x∷xs = [] , (~-nil , l~x∷xs)
~-uncons {xs = y ∷ xs} l~x∷xs = (y ∷ xs) , (~-refl , l~x∷xs)

++-~-∷-move-rl : {l xs ys : List ℕ} {y : ℕ}
                → l ~ (xs ++ y ∷ ys)
                → l ~ (y ∷ xs ++ ys)
++-~-∷-move-rl {xs = []} p = p
++-~-∷-move-rl {xs = x ∷ xs} {ys} {y} p with ~-uncons p
... | ul , ul-perm , recov-l =
  let h-ind = ++-~-∷-move-rl ul-perm
      xh-ind = ~-drop x h-ind
      swap-xy = ~-swap x y (xs ++ ys)
   in ~-trans (~-trans recov-l xh-ind) swap-xy

-- An uncons-free version can be found in the previous commit
-- That version is more rewritable, the current version is the
-- refactored one.

++-~-∷-move-lr : {l xs ys : List ℕ} {y : ℕ}
               → l ~ (y ∷ xs ++ ys)
               → l ~ (xs ++ y ∷ ys)
++-~-∷-move-lr {xs = []} p = p
++-~-∷-move-lr {l} {xs = x ∷ xs} {ys} {y} p
                with ~-uncons {l} {y ∷ xs ++ ys} {x}
                              (~-trans p (~-swap y x (xs ++ ys)))
... | ul , ul-perm , recov-l =
  let h-ind = ++-~-∷-move-lr {ul} {xs} {ys} {y} ul-perm
      xh-ind = ~-drop x h-ind
   in ~-trans recov-l xh-ind

open import Data.List.Properties using (++-identityʳ)

++-comm-~ : {l l' m : List ℕ}
         → l ~ (l' ++ m)
         → l ~ (m ++ l')
++-comm-~ {l' = []} {m = []}    ll'm = ll'm
++-comm-~ {l' = []} {m = z ∷ m} ll'm rewrite ++-identityʳ (z ∷ m) = ll'm
++-comm-~ {l' = y ∷ l'} {m = []}    ll'm rewrite ++-identityʳ (y ∷ l') = ll'm
++-comm-~ {l' = y ∷ l'} {m = z ∷ m} ll'm
         with ~-uncons ll'm
... | uy , uy-perm , recov-l
         with ~-uncons (++-~-∷-move-rl uy-perm)
... | uz , uz-perm , recov-uy =
     let h-ind = ++-comm-~ {l' = l'} uz-perm
         zh-ind = ~-drop z h-ind
         zuy = ~-trans recov-uy zh-ind
         y-zuy = ~-drop y zuy
         nl = ~-trans recov-l y-zuy
      in ++-~-∷-move-lr {xs = z ∷ m} nl

divide-list-~ : (x : ℕ) (l : List ℕ) → let le , gr = divide-list x l
                                          in l ~ (le ++ gr)
divide-list-~ x [] = ~-nil
divide-list-~ x (y ∷ l) with ≤-total y x | divide-list-~ x l
... | inj₁ _ | p = ~-drop y p
... | inj₂ _ | p =
  let le , gr = divide-list x l
      yp = ~-drop y p
   in ++-~-∷-move-lr yp

++-~ᴸ : (m : List ℕ) {l l' : List ℕ} → l ~ l' → (m ++ l) ~ (m ++ l')
++-~ᴸ [] p = p
++-~ᴸ (x ∷ m) p = ~-drop x (++-~ᴸ m p)

++-~ : {l l' m m' : List ℕ} → l ~ l' → m ~ m' → (l ++ m) ~ (l' ++ m')
++-~ ~-nil mm' = mm'
++-~ (~-drop x ll') mm' = ~-drop x (++-~ ll' mm')
++-~ {m' = m'} (~-swap x y l) mm' =
  let p1 = ++-~ᴸ (x ∷ y ∷ l) mm'
      p2 = ~-swap x y (l ++ m')
   in ~-trans p1 p2
++-~ (~-trans {l' = l'} ll'' l''l') mm' =
  let p1 = ++-~ ll'' mm'
      p2 = ++-~ l''l' mm'
      p3 = ++-~ᴸ l' (~-sym mm')
   in ~-trans p1 (~-trans p3 p2)

quicksort-~ : (n : ℕ) (l : List ℕ) (p : length l ≤ n) → l ~ (quicksort-fuel l n p)
quicksort-~ n [] p = ~-nil
quicksort-~ (suc n) (x ∷ l) (s≤s p) with divide-list-less x l
... | lenle , lengr =
  let le , gr = divide-list x l
      le-permuted = quicksort-~ n le (≤-trans lenle p)
      gr-permuted = quicksort-~ n gr (≤-trans lengr p)
      xgr-permuted = ~-drop x gr-permuted
      concat = ++-~ le-permuted xgr-permuted

      div-~ = divide-list-~ x l
      xdiv-~ = ~-drop x div-~
      midx-div-~ = ++-~-∷-move-lr {xs = le} xdiv-~
   in ~-trans midx-div-~ concat

quicksort-permutes : (l : List ℕ) → l ~ (quicksort l)
quicksort-permutes l = quicksort-~ (length l) l ≤-refl

quicksort-is-correct : Correct-Sorting-Algorithm quicksort
quicksort-is-correct l = quicksort-sorts l , quicksort-permutes l

