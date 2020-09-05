module Equality where

infix 4 _≡_
data _≡_ {A : Set} (x :  A) : A → Set where
  refl : x ≡ x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong {A} {B} f {x} {y} refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subt : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subt P refl Px = Px

module ≡-Reasoning {A : Set} where

  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
    -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
    -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
    -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
    -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

trans' : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ


infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

module ≤-Reasoning where

  infix 1 ≤begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix 3 _qed

  ≤begin_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  ≤begin_ x = x

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  .zero ≤⟨ z≤n ⟩ y≤z = z≤n
  (suc p) ≤⟨ s≤s r ⟩ s≤s s = s≤s ( p ≤⟨ r ⟩ s)

  _qed : ∀ (x : ℕ)  → x ≤ x
  zero qed = z≤n
  suc x qed = s≤s (x qed)

open ≤-Reasoning

infixl 5 _+_

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-comm : ∀ (m n : ℕ) → m + n ≡  n + m
  -- sym : ∀ (m n : ℕ) → m ≡ n → n ≡ m
  ≤-refl : ∀ {m n : ℕ} → m ≡ n → m ≤ n
  ≤-+ : ∀ {m n p : ℕ} → m ≤ n → m + p ≤ n + p
  -- comm : ∀ (m n : ℕ) → m + n ≡  n + m
-- Monotonicity

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → (n + p) ≤ (n + q)
+-monoʳ-≤ zero p q p≤q =
  ≤begin
     p
  ≤⟨⟩
    zero + p
  ≤⟨ p≤q ⟩
    zero + q
  qed

+-monoʳ-≤ (suc n) p q p≤q =
  ≤begin
   (suc n) + p
   ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
   (suc n) + q
  qed

{-# BUILTIN EQUALITY _≡_ #-}

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n zero m≤n =
  ≤begin
    m + zero
    ≤⟨ ≤-refl (+-identity m) ⟩
    m
  ≤⟨ m≤n ⟩
    n
  ≤⟨ ≤-refl (sym (+-identity n)) ⟩
    n + zero
  qed
+-monoˡ-≤ m n (suc p) m≤n rewrite +-suc m p | +-suc n p = s≤s (≤-+ m≤n)
  -- ≤begin
  --   m + suc p
  -- ≡⟨ ? ⟩
  --   suc (m + p)
  -- ≤⟨ {!!} ⟩
  --   n + suc p
  -- qed

-- +-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p  = {!!}
-- +-monoʳ-≤ p m n m≤n

-- +-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
-- +-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
