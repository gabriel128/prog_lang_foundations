module Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    (suc 2) + (suc 3)
  ≡⟨⟩
    (suc (suc 1)) + (suc (suc 2))
  ≡⟨⟩
    (suc (suc (suc zero))) + (suc (suc (suc (suc zero))))
  ≡⟨⟩
    suc ((suc (suc zero)) + (suc (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc (suc zero) + (suc (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc (suc (zero + (suc (suc (suc (suc zero)))))))
  ≡⟨⟩
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    7
  ∎

-- Multiplication

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)


_ =
  begin
    2 ^ 4
  ≡⟨⟩
    2 * (2 ^ 3)
  ≡⟨⟩
    2 * (2 * (2 ^ 2))
  ≡⟨⟩
    2 * (2 * (2 * (2 ^ 1)))
  ≡⟨⟩
    2 * (2 * (2 * (2 ^ 1)))
  ≡⟨⟩
    2 * (2 * (2 * (2 * (2 ^ 0))))
  ≡⟨⟩
    2 * (2 * (2 * (2 * (1))))
  ≡⟨⟩
   16
  ∎


-- Monus

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎


infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

_ = inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ =
  begin
    inc (⟨⟩ I O I I)
  ≡⟨⟩
    inc (⟨⟩ I O I) O
  ≡⟨⟩
    inc (⟨⟩ I O) O O
  ≡⟨⟩
    (⟨⟩ I I) O O
  ≡⟨⟩
    ⟨⟩ I I O O
  ∎

to : ℕ → Bin
to zero = ⟨⟩
to (suc x) = inc (to x)

_ : to (suc (suc zero)) ≡ ⟨⟩ I O
_ =
  begin
    to (suc (suc zero))
  ≡⟨⟩
    inc (to (suc zero))
  ≡⟨⟩
    inc (inc ⟨⟩)
  ≡⟨⟩
    inc (⟨⟩ I)
  ≡⟨⟩
    (inc ⟨⟩) O
  ≡⟨⟩
    ⟨⟩ I O
  ∎

from : Bin → ℕ
from x = expFrom x 0
  where
    expFrom : Bin → ℕ → ℕ
    expFrom ⟨⟩ _ = 0
    expFrom (x O) exp = expFrom x (exp + 1)
    expFrom (x I) exp = (expFrom x (exp + 1)) + (2 ^ exp)


_ =
  begin
    from (⟨⟩ I O)
  ≡⟨⟩
    suc (suc zero)
  ∎

_ =
  begin
    from (⟨⟩ I I)
   ≡⟨⟩
    suc (suc (suc zero))
  ∎

_ =
  begin
    from (⟨⟩ I O O)
  ≡⟨⟩
    4
  ∎

example1 : from (⟨⟩ I I O) ≡ 6
example1 = refl
