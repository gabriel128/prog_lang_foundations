module Induction1 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- Associativity

assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- Lemma Right Identity --

identityʳ : ∀ (m : ℕ) → m + zero ≡ m
identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (identityʳ m) ⟩
    suc m
  ∎


-- Lema right suc

+suc : ∀ (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

-- Commutativity

+comm : ∀ (m n : ℕ) → m + n ≡ n + m
+comm zero n =
  begin
    zero + n
  ≡⟨⟩
    n
  ≡⟨ sym (identityʳ n) ⟩
    n + zero
  ∎
+comm (suc m) n =
  begin
    (suc m) + n
  ≡⟨⟩
    suc (m + n)
  ≡⟨ cong suc (+comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (+suc n m) ⟩
    n + suc m
  ∎

-- Show m + (n + p) ≡ n + (m + p)
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+comm m n) ⟩
    (n + m) + p
  ≡⟨ assoc n m p ⟩
    n + (m + p)
  ∎

-- Distributibity

*-nullR : ∀ (m : ℕ) → m * zero ≡ zero
*-nullR zero = refl
*-nullR (suc m) rewrite *-nullR m = refl

distrib : ∀ (m n p) → (m + n) * p ≡ m * p + n * p
distrib zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    zero + n * p
  ≡⟨⟩
    zero * p + n * p
  ∎

distrib (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (distrib m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    (suc m * p) + n * p
  ∎

*-multR : ∀ (m n : ℕ) → m * (suc n) ≡ m + (m * n)
*-multR zero n =
  begin
    zero * (suc n)
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero + zero
  ≡⟨⟩
    zero + (zero * n)
  ∎

*-multR (suc m) n =
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + (m * suc n)
  ≡⟨ cong ((suc n) +_ ) (*-multR m n) ⟩
    (suc n) + (m + m * n)
  ≡⟨ sym (assoc (suc n) m (m * n)) ⟩
    (suc n) + m + m * n
  ≡⟨⟩
    suc (n + m) + (m * n)
  ≡⟨ cong ( _+ (m * n)) (cong suc (+comm n m)) ⟩
    suc (m + n) + (m * n)
  ≡⟨⟩
    suc m + n + m * n
  ≡⟨ assoc (suc m) n (m * n) ⟩
    suc m + (n + m * n)
  ≡⟨⟩
    suc m + (suc m * n)
  ∎


*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n =
  begin
    zero * n
  ≡⟨⟩
    zero
  ≡⟨ sym (*-nullR n) ⟩
    n * zero
  ∎
*-comm (suc m) n =
  begin
    (suc m) * n
  ≡⟨⟩
    n + (m * n)
  ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + (n * m)
  ≡⟨ sym (*-multR n m) ⟩
    n * (suc m)
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite distrib n (m * n) p | *-assoc m n p = refl

-null : ∀ (n : ℕ) → zero ∸ n ≡ zero
-null zero = refl
-null (suc n) = refl


_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)

*-swap : ∀ (a b c d : ℕ) → ((a * b) * c) * d ≡ ((a * c) * b) * d
*-swap a b c d rewrite *-assoc a b c | *-comm b c | sym (*-assoc a c b) = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite identityʳ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p =
  begin
    m * (m ^ (n + p))
  ≡⟨ cong (m *_) (^-distribˡ-+-* m n p) ⟩
    m * ((m ^ n) * (m ^ p))
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m * (m ^ n) * (m ^ p)
  ∎

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) =
  begin
    m * n * ((m * n) ^ p)
  ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
    m * n * ((m ^ p) * (n ^ p))
  ≡⟨⟩
    m * n * ((m ^ p) * (n ^ p))
  ≡⟨ sym (*-assoc (m * n) (m ^ p) (n ^ p)) ⟩
    m * n * (m ^ p) * (n ^ p)
  ≡⟨ *-swap m n (m ^ p) (n ^ p) ⟩
    m * (m ^ p) * n * (n ^ p)
  ≡⟨ *-assoc ((m * (m ^ p))) n (n ^ p) ⟩
    m * (m ^ p) * (n * (n ^ p))
  ∎

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-nullR n = refl
^-*-assoc m n (suc p) =
  begin
    (m ^ n) * ((m ^ n) ^ p)
  ≡⟨ cong ((m ^ n) *_) (^-*-assoc m n p) ⟩
    (m ^ n) * (m ^ (n * p))
  ≡⟨ sym (^-distribˡ-+-* m n (n * p)) ⟩
    (m ^ (n + n * p))
  ≡⟨ cong (m ^_) ((sym (*-multR n p))) ⟩
    (m ^ (n * suc p))
  ∎
