module Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm)


data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

{-
Reflexive: For all n, the relation n ≤ n holds.
Transitive: For all `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p` hold, then `m ≤ p` holds.
Anti-symmetric: For all `m` and `n`, if both `m ≤ n` and `n ≤ m` hold, then `m ≡ n` holds.
Total: For all `m` and `n`, either `m ≤ n` or `n ≤ m`
-}

{-
  Example of a preorder that is not a partial order.
  (⊐, {1,2,3})
  =
  {(1,1), (1,2), (2,1), (2,2), (3, 3), (1,3)}

  Example of a partial order that is not a total order.

  (⊂, 𝒫({a, b}))
  =
  (⊂, {{}, {a}, {b}, {a, b}})

  {reflxive_tuples..., ({},{a}), ({},{b}), ({},{a, b}), ({a}, {a,b}), ({b}, {a,b})}


#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

```
They are vacuosly true, i.e (zero <= suc n, suc <= zero) is false in any combinatino
```

-}

-- REFLEXIVITY

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- Transitivity

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

≤-trans′ : ∀ (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)

-- Anti-symmetric

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

-- Total

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

data Total′ : ℕ → ℕ → Set where
  forward′ : ∀ {m n : ℕ} → m ≤ n → Total′ m n
  flipped′ : ∀ {m n : ℕ} → n ≤ m → Total′ m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
    helper : Total m n → Total (suc m) (suc n)
    helper (forward m≤n)  =  forward (s≤s m≤n)
    helper (flipped n≤m)  =  flipped (s≤s n≤m)

-- Monotonicity

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

{-
#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

-}

-- *-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
-- *-monoʳ-≤ zero p q p≤q = z≤n
-- -- *-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)
-- *-monoʳ-≤ (suc n) p q p≤q  =  s≤s (*-monoʳ-≤ n p q p≤q)

-- Strict inequality

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

{-

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

-}

<-trans : ∀ (m n p : ℕ)
  → m < n
  → n < p
  --------
  → m < p
<-trans zero (suc n) (suc p) z<s _ = z<s
<-trans (suc m) (suc n) (suc p) (s<s n<p) (s<s m<p) = s<s (<-trans m n p n<p m<p)

{-
#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.

-}


data Trichotomy (m n : ℕ) : Set where
  leftTr : m < n → Trichotomy  m n
  rightTr : n < m → Trichotomy m n
  equalTr : m ≡ n → Trichotomy m n

<-trich : ∀ (m n : ℕ) → Trichotomy m n
<-trich zero (suc n) = leftTr z<s
<-trich (suc n) zero = rightTr z<s
<-trich zero zero = equalTr refl
<-trich (suc m) (suc n) with <-trich m n
...                     | leftTr  m<n = leftTr (s<s m<n)
...                     | rightTr n<m = rightTr (s<s n<m)
...                     | equalTr m=n = equalTr (cong suc m=n)
-- <-trich (suc m) (suc n) = induct (<-trich m n)
-- where
--   induct : Trichotomy m n → Trichotomy (suc m) (suc n)
--   induct = {!!}


{-
#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

-}

+<-monoR : ∀ (n p q : ℕ)
  → p < q
  ----------
  → n + p < n + q
+<-monoR zero p q p<q = p<q
+<-monoR (suc n) p q p<q = s<s (+<-monoR n p q p<q)

+<-monoL : ∀ (m n p : ℕ)
  → m < n
  ----------
  → m + p < n + p
+<-monoL m n p m<n rewrite +-comm m p | +-comm n p = +<-monoR p m n m<n

+<-mono : ∀ (m n p q : ℕ)
  → m < n
  → p < q
  --------
  → m + p < n + q
+<-mono m n p q m<n p<q = <-trans (m + p) (n + p) (n + q) (+<-monoL m n p m<n) (+<-monoR n p q p<q)

{-

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

-}

<-suc : ∀ (n : ℕ) → n < suc n
<-suc zero = z<s
<-suc (suc r) = s<s (<-suc r)

<-mono-succ : ∀ {m n : ℕ} → m < n → m < suc n
<-mono-succ z<s = z<s
<-mono-succ (s<s r) = s<s (<-mono-succ r)


≤-impl-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-impl-< zero (suc n) (s≤s m≤n) = z<s {n}
≤-impl-< (suc m) (suc n) (s≤s m≤n) =
  let r = ≤-impl-< m n m≤n
  in s<s r

-- ≤-impl-< zero (suc n) m≤n = z<s
-- ≤-impl-< (suc m) (suc n) (s≤s m≤n) = s<s (≤-impl-< m n m≤n)

<-impl-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-impl-≤ z<s = s≤s z≤n
<-impl-≤ (s<s m<n) = s≤s (<-impl-≤ m<n)
