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
