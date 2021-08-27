open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤-pred : {m n : ℕ} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s m≤n) = m≤n

≤-suc : {m n : ℕ} → m ≤ n → suc m ≤ suc n
≤-suc = s≤s

≤s : (n : ℕ) → n ≤ suc n
≤s zero = z≤n
≤s (suc n) = s≤s (≤s n)

≤-sucᴿ : {m n : ℕ} → m ≤ n → m ≤ suc n
≤-sucᴿ z≤n = z≤n
≤-sucᴿ (s≤s p) = s≤s (≤-sucᴿ p)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : {m n p : ℕ} → (m ≤ n) → (n ≤ p) → (m ≤ p)
≤-trans z≤n np = z≤n
≤-trans (s≤s mn) (s≤s np) = s≤s (≤-trans mn np)

_≤?_ : (m n : ℕ) → (m ≤ n) ⊎ (n ≤ m)
zero ≤? n = inj₁ z≤n
suc m ≤? zero = inj₂ z≤n
suc m ≤? suc n with m ≤? n
... | inj₁ mn = inj₁ (s≤s mn)
... | inj₂ nm = inj₂ (s≤s nm)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; _∷_; [])

{-
   Less Than All Relation
-}

_≤*_ : (x : ℕ) → (l : List ℕ) → Set
x ≤* [] = ⊤
x ≤* (y ∷ l) = (x ≤ y) × (x ≤* l)

example-≤* : 2 ≤* (3 ∷ 2 ∷ 5 ∷ [])
example-≤* = s≤s (s≤s z≤n) , s≤s (s≤s z≤n) , s≤s (s≤s z≤n) , tt

open import Relation.Nullary using (¬_)

example-≰* : ¬ 3 ≤* (3 ∷ 2 ∷ 5 ∷ [])
example-≰* (3≤3 , s≤s (s≤s ()) , _)

sorted : (l : List ℕ) → Set
sorted [] = ⊤
sorted (x ∷ l) = x ≤* l × sorted l

example1-sorted : sorted (1 ∷ 2 ∷ [])
example1-sorted = (s≤s z≤n , tt) , tt , tt

{-
   Permutations
-}

data _~_ {A : Set} : List A → List A → Set where
  ~-nil : [] ~ []
  ~-drop : (x : A) { l l' : List A} → l ~ l' → (x ∷ l) ~ (x ∷ l')
  ~-swap : (x y : A) (l : List A) → (x ∷ y ∷ l) ~ (y ∷ x ∷ l)
  ~-trans : {l l' l'' : List A} → l ~ l' → l' ~ l'' → l ~ l''

example-perm-1 : (3 ∷ 1 ∷ 2 ∷ []) ~ (1 ∷ 2 ∷ 3 ∷ [])
example-perm-1 =
  let p1 = ~-drop 1 (~-swap 3 2 [])
      p2 = ~-swap 3 1 (2 ∷ [])
   in ~-trans p2 p1

~-refl : {A : Set} {l : List A} → l ~ l
~-refl {_} {[]} = ~-nil
~-refl {_} {x ∷ l} = ~-drop x ~-refl

~-sym : {A : Set} {l l' : List A} → l ~ l' → l' ~ l
~-sym ~-nil = ~-nil
~-sym (~-drop x l~l') = ~-drop x (~-sym l~l')
~-sym (~-swap x y l) = ~-swap y x l
~-sym (~-trans l~l'' l''~l) = ~-trans (~-sym l''~l) (~-sym l~l'')

{-
   Insertion sort
-}

insert : (x : ℕ) → (l : List ℕ) → List ℕ
insert x [] = x ∷ []
insert x (y ∷ l) with x ≤? y
... | inj₁ xy = x ∷ y ∷ l
... | inj₂ yx = y ∷ insert x l

sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ l) = insert x (sort l)

example1 : List ℕ
example1 = sort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

≤*-insert : (x y : ℕ) (l : List ℕ) → x ≤ y → x ≤* l → x ≤* insert y l
≤*-insert x y [] x≤y x≤*l = x≤y , tt
≤*-insert x y (z ∷ l) x≤y (x≤z , z≤*l) with y ≤? z
... | inj₁ y≤z = x≤y , x≤z , z≤*l
... | inj₂ z≤y = x≤z , ( ≤*-insert x y l x≤y z≤*l )

≤*-trans : {x y : ℕ} {l : List ℕ} → x ≤ y → y ≤* l → x ≤* l
≤*-trans {l = []} x≤y y≤*l = tt
≤*-trans {l = z ∷ l} x≤y (x≤z , y≤*l) = ≤-trans x≤y x≤z , ≤*-trans x≤y y≤*l

insert-sorting : (x : ℕ) → (l : List ℕ) → sorted l → sorted (insert x l)
insert-sorting x [] sl = tt , tt
insert-sorting x (y ∷ l) (y≤*l , sl) with x ≤? y
... | inj₁ x≤y = (x≤y , ≤*-trans x≤y y≤*l) , y≤*l , sl
... | inj₂ y≤x = ≤*-insert y x l y≤x y≤*l , insert-sorting x l sl 

sort-sorts : ∀ (l : List ℕ) → sorted (sort l)
sort-sorts [] = tt
sort-sorts (x ∷ l) = insert-sorting x (sort l) (sort-sorts l)

insert-~ : (x : ℕ) (l : List ℕ) → (x ∷ l) ~ (insert x l)
insert-~ x [] = ~-drop x ~-nil
insert-~ x (y ∷ l) with x ≤? y
... | inj₁ x≤y = ~-refl
... | inj₂ y≤x = ~-trans (~-swap x y l) (~-drop y (insert-~ x l))

~-insert : (x : ℕ) {l l' : List ℕ} → l ~ l' → insert x l ~ insert x l'
~-insert x {l} {l'} l~l' =
  let a = ~-sym (insert-~ x l)
      b = insert-~ x l'
      c = ~-drop x l~l'
    in ~-trans (~-trans a c) b

sort-~ : (l : List ℕ) → l ~ (sort l)
sort-~ [] = ~-nil
sort-~ (x ∷ l) = ~-trans (~-drop x (sort-~ l)) (insert-~ x (sort l))

insert-sort-correct : (l : List ℕ) → sorted (sort l) × l ~ sort l
insert-sort-correct l = sort-sorts l , sort-~ l

{-
   No sort
-}

no-sort : List ℕ → List ℕ
no-sort [] = []
no-sort (_ ∷ _) = []

no-sort-sorts : ∀ (l : List ℕ) → sorted (no-sort l)
no-sort-sorts [] = tt
no-sort-sorts (_ ∷ _) = tt

{-
   Merge sort
-}

open import Data.List using (_++_)

split : {A : Set} → List A → List A × List A
split [] = [] , []
split (x ∷ []) = x ∷ [] , []
split (x ∷ y ∷ l) with split l
... | xs , ys = (x ∷ xs) , (y ∷ ys)

merge : (l m : List ℕ) → List ℕ
merge' : ℕ → (l m : List ℕ) → List ℕ

merge (x ∷ l) (y ∷ m) with x ≤? y
... | inj₁ x≤y = x ∷ merge l (y ∷ m)
... | inj₂ y≤x = y ∷ merge' x l m
merge l m = l ++ m

merge' x l (y ∷ m) with x ≤? y
... | inj₁ x≤y = x ∷ merge l (y ∷ m)
... | inj₂ y≤x = y ∷ merge' x l m
merge' x l [] = x ∷ l

-- {-# TERMINATING #-}
-- mergesort : List ℕ → List ℕ
-- mergesort [] = []
-- mergesort (x ∷ []) = x ∷ []
-- mergesort l with split l
-- ... | l , m = merge (mergesort l) (mergesort m)

_<_ : (x y : ℕ) → Set
x < y = suc x ≤ y

open import Data.Product using (proj₁; proj₂)

length : {A : Set} (l : List A) → ℕ
length [] = zero
length (_ ∷ l) = suc (length l)

split-less : {x y : ℕ} (l : List ℕ) → let l' = x ∷ y ∷ l
                                          xs , ys = split l'
                                        in length xs < length l' × length ys < length l'
split-less [] = s≤s (s≤s z≤n) , s≤s (s≤s z≤n)
split-less (z ∷ []) = s≤s (s≤s (s≤s z≤n)) , s≤s (s≤s z≤n)
split-less lz@(z ∷ z' ∷ l) with split-less {z} {z'} l
... | s≤s (s≤s p1) , s≤s (s≤s p2) = s≤s (s≤s (s≤s (≤-sucᴿ p1))) , s≤s (s≤s (s≤s (≤-sucᴿ p2)))

mergesort-fuel : (n : ℕ) → (l : List ℕ) → (length l ≤ n) → List ℕ
mergesort-fuel n [] p = []
mergesort-fuel n (x ∷ []) p = x ∷ []
mergesort-fuel (suc n) l@(a ∷ b ∷ l') (s≤s p) with split-less {a} {b} l'
... | s≤s p1 , s≤s p2 =
  let xs , ys = split (a ∷ b ∷ l')
    in merge (mergesort-fuel n xs (≤-trans p1 p)) (mergesort-fuel n ys (≤-trans p2 p))

mergesort : (l : List ℕ) → List ℕ
mergesort l = mergesort-fuel (length l) l (≤-refl (length l))

test-merge : List ℕ
test-merge = mergesort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

-- mergesort-sorting : (l : List ℕ) → sorted (mergesort-fuel (length l) l (≤-refl (length l)))
-- mergesort-sorting [] = tt
-- mergesort-sorting (x ∷ []) = tt , tt
-- mergesort-sorting (x ∷ y ∷ l) = {!!}

--
-- QUICKSORT
-- 

divide-lists : ℕ → List ℕ → List ℕ × List ℕ
divide-lists x [] = [] , []
divide-lists x (y ∷ l) with divide-lists x l | y ≤? x
... | l , g | inj₁ y≤x = (y ∷ l) , g
... | l , g | inj₂ x≤y = l , (y ∷ g)

-- {-# TERMINATING #-}
-- quicksort' : List ℕ → List ℕ
-- quicksort' [] = []
-- quicksort' (x ∷ l) =
--   let le , gr = divide-lists x l
--   in quicksort' le ++ (x ∷ []) ++ quicksort' gr

-- example-quicksort' = quicksort' (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

divide-lists-less : (x : ℕ) → (l : List ℕ) → let le , gr = divide-lists x l
                                               in length le ≤ length l × length gr ≤ length l
divide-lists-less _ [] = z≤n , z≤n
divide-lists-less x (y ∷ l) with divide-lists-less x l | y ≤? x
... | p1 , p2 | inj₁ y≤x = s≤s p1 , ≤-sucᴿ p2
... | p1 , p2 | inj₂ x≤y = (≤-sucᴿ p1) , (s≤s p2)

quicksort-fuel : (l : List ℕ) → (n : ℕ) → (length l ≤ n) → List ℕ
quicksort-fuel [] n p = []
quicksort-fuel (x ∷ l) (suc n) (s≤s p) with divide-lists-less x l
... | le≤l , gr≤l = let le , gr = divide-lists x l
                    in     (quicksort-fuel le n (≤-trans le≤l p))
                        ++ (x ∷ [])
                        ++ (quicksort-fuel gr n (≤-trans gr≤l p))

quicksort : List ℕ → List ℕ
quicksort l = quicksort-fuel l (length l) (≤-refl (length l))

_≥*_ : ℕ → List ℕ → Set
x ≥* [] = ⊤
x ≥* (y ∷ ys) = y ≤ x × x ≥* ys

++-≤* : {x : ℕ} {xs ys : List ℕ} → x ≤* xs → x ≤* ys → x ≤* (xs ++ ys)
++-≤* {xs = []} xlesxs xlesys = xlesys
++-≤* {xs = z ∷ xs} (x≤z , x≤*xs) xlesys = x≤z , ++-≤* x≤*xs xlesys

++-≥* : {x : ℕ} {xs ys : List ℕ} → x ≥* xs → x ≥* ys → x ≥* (xs ++ ys)
++-≥* {xs = []} xgesxs xgesys = xgesys
++-≥* {xs = z ∷ xs} (z≤x , x≥*xs) xgesys = z≤x , ++-≥* x≥*xs xgesys

divide-lists-compare : (x : ℕ) → (l : List ℕ) → let le , gr = divide-lists x l
                                                  in x ≥* le × x ≤* gr
divide-lists-compare x [] = tt , tt
divide-lists-compare x (y ∷ l) with divide-lists x l | divide-lists-compare x l | y ≤? x
... | le , gr | x≥*le , x≤*gr | inj₁ y≤x = (y≤x , x≥*le) , x≤*gr
... | le , gr | x≥*le , x≤*gr | inj₂ x≤y = x≥*le , (x≤y , x≤*gr)

divide-lists-preserves-≤* : (x : ℕ) {y : ℕ} (l : List ℕ)
                          → x ≤* l
                          → let le , gr = divide-lists y l
                             in x ≤* le × x ≤* gr
divide-lists-preserves-≤* x {y} []      xlesl = tt , tt
divide-lists-preserves-≤* x {y} (z ∷ l) (x≤z , xlesl) with z ≤? y
... | inj₁ _ =
  let xlesle , xlesgr = divide-lists-preserves-≤* x {y} l xlesl
   in (x≤z , xlesle) , xlesgr
... | inj₂ _ =
  let xlesle , xlesgr = divide-lists-preserves-≤* x {y} l xlesl
    in xlesle , (x≤z , xlesgr)

divide-lists-preserves-≥* : (x : ℕ) {y : ℕ} (l : List ℕ) → x ≥* l → let le , gr = divide-lists y l
                                                                     in x ≥* le × x ≥* gr
divide-lists-preserves-≥* x {y} [] xgesl = tt , tt
divide-lists-preserves-≥* x {y} (z ∷ l) (z≤x , x≥*l) with z ≤? y
... | inj₁ _ =
   let xgesle , xgesgr = divide-lists-preserves-≥* x {y} l x≥*l
    in (z≤x , xgesle) , xgesgr
... | inj₂ _ =
   let xgesle , xgesgr = divide-lists-preserves-≥* x {y} l x≥*l
    in xgesle , (z≤x , xgesgr)

quicksort-preserves-≤* : (x : ℕ) (l : List ℕ) {n : ℕ} {p : length l ≤ n} → x ≤* l → x ≤* quicksort-fuel l n p
quicksort-preserves-≤* x [] xlesl = tt
quicksort-preserves-≤* x (y ∷ l) {suc n} {s≤s p} (x≤y , x≤*l)
  with divide-lists-less y l | divide-lists-compare y l
... | lenle , lengr | fst , ylesgr =
  let le , gr = divide-lists y l
      xlesle , xlesgr = divide-lists-preserves-≤* x {y} l x≤*l
      sle = quicksort-fuel le n (≤-trans lenle p)
      sgr = quicksort-fuel gr n (≤-trans lengr p)
      abc = quicksort-preserves-≤* y gr {n} {≤-trans lengr p} ylesgr
      t1 : x ≤* (y ∷ sgr)
      t1 = x≤y , (≤*-trans x≤y abc)
      t2 : x ≤* sle
      t2 = quicksort-preserves-≤* x le {n} {≤-trans lenle p} xlesle
   in ++-≤* t2 t1

quicksort-preserves-≥* : (x : ℕ) (l : List ℕ) {n : ℕ} {p : length l ≤ n} → x ≥* l → x ≥* quicksort-fuel l n p
quicksort-preserves-≥* x [] xlesl = tt
quicksort-preserves-≥* x (y ∷ l) {suc n} {s≤s p} (y≤x , x≥*l)
  with divide-lists-less y l | divide-lists-compare y l
... | lenle , lengr | y≥*le , y≤*gr =
  let le , gr = divide-lists y l
      xgesle , xgesgr = divide-lists-preserves-≥* x {y} l x≥*l
      sle = quicksort-fuel le n (≤-trans lenle p)
      sgr = quicksort-fuel gr n (≤-trans lengr p)
      t1 : x ≥* (y ∷ sgr)
      t1 = y≤x , (quicksort-preserves-≥* x gr {n} {≤-trans lengr p} xgesgr)
      t2 : x ≥* sle
      t2 = quicksort-preserves-≥* x le {n} {≤-trans lenle p} xgesle
   in ++-≥* t2 t1

join-sorted : (x : ℕ) (l m : List ℕ)
            → sorted l → sorted m
            → x ≥* l → x ≤* m
            → sorted (l ++ (x ∷ []) ++ m)
join-sorted x [] m sl sm xgesl xlesm = xlesm , sm
join-sorted x (y ∷ l) m (y≤*l , sl) sm (y≤x , x≥*l) xlesm =
  let y≤*m = ≤*-trans y≤x xlesm
   in ++-≤* y≤*l (y≤x , y≤*m) , join-sorted x l m sl sm x≥*l xlesm

quicksort-sorts : (n : ℕ) (l : List ℕ) (p : length l ≤ n) → sorted (quicksort-fuel l n p)
quicksort-sorts zero [] p = tt
quicksort-sorts (suc n) [] p = tt
quicksort-sorts (suc n) (x ∷ l) (s≤s p) with divide-lists-less x l | divide-lists-compare x l
... | p1 , p2 | xgesle , xlesgr =
  let le , gr = divide-lists x l
      le-sorted = quicksort-sorts n le (≤-trans p1 p)
      gr-sorted = quicksort-sorts n gr (≤-trans p2 p)
      les = quicksort-fuel le n (≤-trans p1 p)
      grs = quicksort-fuel gr n (≤-trans p2 p)
    in join-sorted x les grs le-sorted gr-sorted
                     (quicksort-preserves-≥* x le xgesle)
                     (quicksort-preserves-≤* x gr xlesgr)

quicksort-sorting : (l : List ℕ) → sorted (quicksort l)
quicksort-sorting l = quicksort-sorts (length l) l (≤-refl (length l))

test-quicksort : List ℕ
test-quicksort = quicksort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

open import Data.List.Properties using (++-identityʳ)

open import Data.Product using (Σ)

++-~-cons : {l xs : List ℕ} {x : ℕ} → l ~ (x ∷ xs) → Σ (List ℕ) (λ l' → l' ~ xs × l ~ (x ∷ l'))
++-~-cons {xs = []} {x = x} p1 = [] , (~-nil , p1)
++-~-cons {xs = y ∷ xs} {x = x} p1 = (y ∷ xs) , (~-refl , p1)

~-++-one : {y : ℕ} {l xs ys : List ℕ} → l ~ (xs ++ y ∷ ys) → l ~ (y ∷ xs ++ ys)
~-++-one {xs = []} p1 = p1
~-++-one {y} {xs = x ∷ xs} {ys = ys} p1 with ++-~-cons p1
... | ln , ln-perm , recovln =
  let abc1 = ~-drop x (~-++-one ln-perm)
      t1 = ~-trans recovln abc1
      s = ~-swap x y (xs ++ ys)
   in ~-trans t1 s

~-++-insert : {y : ℕ} {l xs ys : List ℕ} → l ~ (y ∷ xs ++ ys) → l ~ (xs ++ y ∷ ys)
~-++-insert {xs = []} p1 = p1
~-++-insert {y} {xs = x ∷ xs} {ys = ys} p1 with ++-~-cons (~-trans p1 (~-swap y x (xs ++ ys)))
... | ln , ln-perm , recovln =
  let abc1 = ~-++-insert {xs = xs} ln-perm
      t1 = ~-drop x abc1
   in ~-trans recovln t1

++-comm~ : {l l' m : List ℕ} → l ~ (l' ++ m) → l ~ (m ++ l')
++-comm~ {l' = []} {m = []} ll'm = ll'm
++-comm~ {l' = []} {m = x ∷ m} ll'm rewrite ++-identityʳ (x ∷ m) = ll'm
++-comm~ {l' = x ∷ l'} {m = []} ll'm rewrite ++-identityʳ (x ∷ l') = ll'm
++-comm~ {l} {y ∷ l'} {m = z ∷ m} ll'm with ++-~-cons ll'm
... | ln , ln-perm , recovln with ++-~-cons (~-++-one ln-perm)
... | ln' , ln'-perm , recovln' =
  let p1 = ++-comm~ {ln'} {l'} {m} ln'-perm
      abc1 = ~-drop z p1
      t1 = ~-trans recovln' abc1
      abc2 = ~-drop y t1
      t2 = ~-trans recovln abc2
   in ~-++-insert {xs = z ∷ m} t2

divide-lists-~ : (x : ℕ) (l : List ℕ) → let le , gr = divide-lists x l
                                          in l ~ (le ++ gr)
divide-lists-~ x [] = ~-nil
divide-lists-~ x (y ∷ l) with y ≤? x | divide-lists-~ x l
... | inj₁ _ | p = ~-drop y p
... | inj₂ _ | p =
  let le , gr = divide-lists x l
      c1 = ++-comm~ {l} {le} p
      c2 = ~-drop y c1
      c3 = ++-comm~ {y ∷ l} {y ∷ gr} c2
   in c3

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
quicksort-~ (suc n) (x ∷ l) (s≤s p) with divide-lists-less x l
... | p1 , p2 =
  let le , gr = divide-lists x l
      le-permuted = quicksort-~ n le (≤-trans p1 p)
      gr-permuted = quicksort-~ n gr (≤-trans p2 p)
      abc = ~-drop x gr-permuted
      abc2 = ++-~ le-permuted abc
      divl = ++-comm~ {l} {le} (divide-lists-~ x l)
      d2 = ~-drop x divl
      d3 = ++-comm~ {x ∷ l} {x ∷ gr} d2
      final : (x ∷ l) ~ (le ++ (x ∷ []) ++ gr)
      final = d3
   in ~-trans final abc2

quicksort-permutes : (l : List ℕ) → l ~ (quicksort l)
quicksort-permutes l = quicksort-~ (length l) l (≤-refl (length l))

quicksort-is-correct : (l : List ℕ) → sorted (quicksort l) × l ~ (quicksort l)
quicksort-is-correct l = quicksort-sorting l , quicksort-permutes l

