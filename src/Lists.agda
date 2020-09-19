module Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import Isomorphismss using (_≃_; _⇔_)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎

++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

-- Length

length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    zero + length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎

length-++ (x ∷ xs) ys =
  begin
    length (x ∷ xs ++ ys)
  ≡⟨⟩
    length (x ∷ (xs ++ ys))
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    (suc (length xs)) + length ys
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

-- Reverse

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

-- Exercise

-- _++_ : ∀ {A : Set} → List A → List A → List A
-- []       ++ ys  =  ys
-- (x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
reverse-++-distrib : ∀ {A : Set } (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib {A} [] ys =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []
  ≡⟨⟩
    reverse ys ++ reverse []
  ∎

-- reverse (x ∷ xs)  =  reverse xs ++ [ x ]
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-involutive : ∀ {A : Set} (xs : List A) →  reverse (reverse xs) ≡ xs
reverse-involutive [] =
  begin
    reverse (reverse [])
  ≡⟨⟩
    reverse []
  ≡⟨⟩
    []
  ∎

-- reverse []        =  []
-- reverse (x ∷ xs)  =  reverse xs ++ [ x ]
-- []       ++ ys  =  ys
-- (x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
-- reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    reverse [ x ] ++ (reverse (reverse xs))
  ≡⟨⟩
    reverse (x ∷ []) ++ (reverse (reverse xs))
  ≡⟨⟩
    (reverse [] ++ [ x ]) ++ (reverse (reverse xs))
  ≡⟨⟩
    [ x ] ++ (reverse (reverse xs))
  ≡⟨ cong ([ x ] ++_) (reverse-involutive xs) ⟩
    [ x ] ++ xs
  ≡⟨⟩
    (x ∷ xs)
  ∎

-- Faster Reverse

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A) → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
   reverse xs
  ∎

-- Map

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎

-- Exercise map-compose (practice)
-- Prove that the map of a composition is equal to the composition of two maps:
-- The last step of the proof requires extensionality.

-- map : ∀ {A B : Set} → (A → B) → List A → List B
-- map f []        =  []
-- map f (x ∷ xs)  =  f x ∷ map f xs
postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

map-compose-extens : ∀ {A B C : Set}
  → (f : A → B)
  → (g : B → C)
  → (xs : List A)
  → map (λ x' → g (f x')) xs ≡ map g (map f xs)
map-compose-extens f g [] = refl
map-compose-extens f g (x ∷ xs) =
  begin
    g (f x) ∷ map (λ x' → g (f x')) xs
  ≡⟨ cong ((g (f x)) ∷_) (map-compose-extens f g xs) ⟩
    g (f x) ∷ map g (map f xs)
  ∎

map-compose : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → map (g ∘ f) ≡ (map g ∘ map f)
map-compose f g =
  begin
    map (g ∘ f)
  ≡⟨ extensionality (λ xs → map-compose-extens f g xs) ⟩
   (map g ∘ map f)
  ∎

-- Exercise map-++-distribute (practice)
-- Prove the following relationship between map and append:

map-++-distribute : ∀ {A B : Set}
  (f : A → B)
  (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys =
  begin
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (f x ∷_) (map-++-distribute f xs ys) ⟩
    f x ∷ map f xs ++ map f ys
  ∎

-- Exercise map-Tree (practice)
-- Define a type of trees with leaves of type A and internal nodes of type B:

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

-- Define a suitable map operator over trees:

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node xs x ys) = node (map-Tree f g xs) (g x) (map-Tree f g ys)


-- Folds

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

-- Exercise product (recommended)
-- Use fold to define a function to find the product of a list of numbers. For example:

product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

-- Exercise foldr-++ (recommended)
-- Show that fold and append are related as follows:

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A)
           → (foldr _⊗_ e (xs ++ ys)) ≡ (foldr _⊗_ (foldr _⊗_ e ys) xs)
foldr-++ _⊗_ e [] ys =
  begin
    foldr _⊗_ e ([] ++ ys)
  ≡⟨⟩
    foldr _⊗_ (foldr _⊗_ e ys) []
  ∎
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin
    (x ⊗ foldr _⊗_ e (xs ++ ys))
  ≡⟨⟩
    foldr _⊗_ e (x ∷ (xs ++ ys))
  ≡⟨⟩
    foldr _⊗_ e ((x ∷ xs) ++ ys)
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
    foldr _⊗_ (foldr _⊗_ e ys) (x ∷  xs)
  ≡⟨⟩
    (x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs)
  ∎

-- Exercise foldr-∷ (practice)
-- Show

foldr-∷ : ∀ {A : Set} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) =
  begin
    x ∷ foldr _∷_ [] xs
  ≡⟨ cong (x ∷_) (foldr-∷ xs) ⟩
    x ∷ xs
  ∎

-- Show as a consequence of foldr-++ above that


foldr-++eq : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
foldr-++eq xs ys rewrite (sym (foldr-∷ ys)) =
  begin
    xs ++ foldr _∷_ [] ys
  ≡⟨ cong (xs ++_) (foldr-∷ ys) ⟩
    xs ++ ys
  ≡⟨ sym (foldr-∷ (xs ++ ys)) ⟩
    foldr _∷_ [] (xs ++ ys)
  ≡⟨ foldr-++ _∷_ [] xs ys ⟩
    foldr _∷_ (foldr _∷_ [] ys) xs
  ∎


-- Exercise map-is-foldr (practice)
-- Show that map can be defined using fold:

-- extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
map-is-foldr' : ∀ {A B : Set} (f : A → B) (xs : List A) → map f xs ≡ foldr (λ x₁ → _∷_ (f x₁)) [] xs
map-is-foldr' f [] = refl
map-is-foldr' f (x ∷ xs) = cong (f x ∷_) (map-is-foldr' f xs)

map-is-foldr : ∀ {A B : Set} (f : A → B) → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality λ xs → map-is-foldr' f xs


-- Exercise fold-Tree (practice)
-- Define a suitable fold function for the type of trees given earlier:

-- data Tree (A B : Set) : Set where
--   leaf : A → Tree A B
--   node : Tree A B → B → Tree A B → Tree A B

fold-tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-tree f g (leaf x) = f x
fold-tree f g (node lhs x rhs) = g (fold-tree f g lhs) x (fold-tree f g rhs)

-- -- Your code goes here
-- Exercise map-is-fold-Tree (practice)
-- Demonstrate an analogue of map-is-foldr for the type of trees.

-- map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
-- map-Tree f g (leaf x) = leaf (f x)
-- map-Tree f g (node xs x ys) = node (map-Tree f g xs) (g x) (map-Tree f g ys)

map-is-fold-tree' : ∀ {A B C D : Set} (f : A → C) (g : B → D) (xs : Tree A B)
                    → map-Tree f g xs ≡ fold-tree (λ x → leaf (f x)) (λ lhs x rhs → node lhs (g x) rhs) xs
map-is-fold-tree' f g (leaf x) = refl
map-is-fold-tree' f g (node lhs x rhs) rewrite map-is-fold-tree' f g lhs | map-is-fold-tree' f g rhs = refl

map-is-fold-tree : ∀ {A B C D : Set} (f : A → C) (g : B → D)
                   → map-Tree f g ≡ fold-tree (λ x → leaf (f x)) (λ lhs x rhs → node lhs (g x) rhs)
map-is-fold-tree f g = extensionality λ tree → map-is-fold-tree' f g tree

-- Exercise sum-downFrom (stretch)
-- Define a function that counts down as follows:

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
-- For example:

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

-- Prove that the sum of the numbers (n - 1) + ⋯ + 0 is equal to n * (n ∸ 1) / 2:

-- []       ++ ys  =  ys
-- (x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
-- foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs
-- (foldr _::_ [] (xs ++ ys)) ≡ (foldr _::_ (foldr _::_ [] ys) xs)

-- _-_ : Nat → Nat → Nat
-- n     - zero = n
-- zero  - suc m = zero
-- suc n - suc m = n - m

  -- n+n*n : (n : ℕ) → n + (n + zero) + n * (n ∸ 1) ≡ n + n * n

-- (suc m) * n  =  n + (m * n)

open import Induction1 using (distrib; *-comm; +suc; *-multR)

n+n≡2n : ∀ {n : ℕ} → n * 2 ≡ n + n
n+n≡2n {zero} = refl
n+n≡2n {suc n} rewrite +suc n n = cong (suc ∘ suc) (n+n≡2n {n})

n-assoc : {n : ℕ} → (n + n + (n + n * n)) ≡ (n + (n + (n + n * n)))
n-assoc {n} rewrite +-assoc n n (n + n * n) = refl

n+n*n : {n : ℕ} → n * 2 + n * (n ∸ 1) ≡ n + n * n
n+n*n {zero} = refl
n+n*n {suc n} rewrite +suc n (n + n * suc n) | *-multR n n | n+n≡2n {n} | n-assoc {n} = refl

-- distrib : ∀ (m n p) → (m + n) * p ≡ m * p + n * p
sum-of-n : ∀ {n : ℕ} → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-of-n {zero} = refl
sum-of-n {suc n} =
  begin
    (n + sum (downFrom n)) * 2
  ≡⟨ distrib n (sum (downFrom n)) 2 ⟩
    n * 2 + sum (downFrom n) * 2
  ≡⟨ cong ((n * 2) +_) (sum-of-n {n}) ⟩
    (n * 2) + n * (n ∸ 1)
  ≡⟨ n+n*n {n} ⟩
    n + n * n
  ∎

-- Monoid

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ (foldr _⊗_ e xs) ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    (foldr _⊗_ e []) ⊗ y
  ∎

foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

  -- foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
  -- foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

-- foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

-- assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
-- identityˡ : ∀ (x : A) → e ⊗ x ≡ x
-- identityʳ : ∀ (x : A) → x ⊗ e ≡ x
-- foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs
-- foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs
-- foldr _⊗_ y xs ≡ (foldr _⊗_ e xs) ⊗ y

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ (y ⊗ (foldl _⊗_ e xs))
foldl-monoid _⊗_ e isMonoid [] y =
  begin
    y
  ≡⟨ sym ((identityʳ isMonoid) y) ⟩
    (y ⊗ e)
  ∎
foldl-monoid _⊗_ e isMonoid (x ∷ xs) y rewrite identityˡ isMonoid x =
  begin
    foldl _⊗_ (y ⊗ x) xs
  ≡⟨ foldl-monoid _⊗_ e isMonoid xs (y ⊗ x) ⟩
    (y ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ assoc isMonoid y x (foldl _⊗_ e xs) ⟩
    (y ⊗ (x ⊗ foldl _⊗_ e xs))
  ≡⟨ cong (y ⊗_) (sym (foldl-monoid _⊗_ e isMonoid xs x)) ⟩
    (y ⊗ foldl _⊗_ x xs)
  ∎

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A)  (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) → foldr _⊗_ e xs  ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e isMonoid [] = refl
foldr-monoid-foldl _⊗_ e isMonoid (x ∷ xs) rewrite identityˡ isMonoid x =
  begin
    (x ⊗ foldr _⊗_ e xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl _⊗_ e isMonoid xs) ⟩
    (x ⊗ (foldl _⊗_ e xs))
  ≡⟨ sym (foldl-monoid _⊗_ e isMonoid xs x) ⟩
    foldl _⊗_ x xs
  ∎
