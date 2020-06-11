module Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
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
