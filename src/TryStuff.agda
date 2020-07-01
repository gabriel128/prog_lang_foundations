module TryStuff where


import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; cong)


-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
-- open import Data.Nat using (ℕ; zero; suc)
-- open import Data.Nat.Properties using (+-comm; *-comm)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Id (A : Set) : Set  where
  pack : A → Id A

data ⊥ : Set where

-- infixl 4 suc
-- infixl 6  _+_≡_

data _+_≡_ : ℕ → ℕ → ℕ → Set where
 z+ : ∀ {n} → zero + n ≡ n
 suc+ : ∀ {n m k} → n + m ≡ k → suc n + m ≡ suc k


data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

_||_ : Bool → Bool → Bool
true || _ = true
false || x = x


infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A


someList : List ℕ
someList = 1 :: 2 :: []

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)


someVec : Vec ℕ (suc (suc zero))
someVec = 1 :: 2 :: []

mapV : {A B : Set} {n : ℕ} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x :: xs) = f x :: mapV f xs

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)

_!_ : {n : ℕ} {A : Set} → Vec A n → Fin n → A
(x :: xs) ! fzero = x
(x :: xs) ! fsuc a = xs ! a


-----

data False : Set where

data True : Set where
  tt : True

isTrue : Bool → Set
isTrue true = True
isTrue false = False

_<_ : ℕ → ℕ → Bool
_ < zero = false
zero < suc y = true
suc x < suc y = x < y

length : {A : Set} → List A → ℕ
length [] = 0
length (_ :: xs) = suc (length xs)

lookup : {A : Set} (xs : List A) → Fin (length xs) → A
lookup (x :: xs) fzero = x
lookup (x :: xs) (fsuc r) = lookup xs r

someList1 : List ℕ
someList1 = 1 :: 2 :: 3 :: []

lookupV : ℕ
lookupV = lookup someList1 (fsuc (fsuc fzero))


-- data _+_≡_ : ℕ → ℕ → ℕ → Set where
--   z+ : ∀ {n} → zero + n ≡ n
--   suc+ : ∀ {n m k} → n + m ≡ k → suc n + m ≡ suc k

-- +-rightZero : ∀ (n : ℕ) → n + zero ≡ n
